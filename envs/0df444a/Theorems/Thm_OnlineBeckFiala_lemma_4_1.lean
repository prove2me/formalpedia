-- Prove2me | Theorems.Thm_OnlineBeckFiala_lemma_4_1
-- name    : OnlineBeckFiala.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:53.605361+00:00
-- url     : https://prove2.me/theorems/cdc34cb7-dae4-488d-8da1-03962786380d
-- title:
--   Lemma 4.1 (Averaging the coordinate costs) — $P\{\sum_{i\le r}W_i>K_\eta d\}\le C_\eta e^{-c_\eta d/\log^{2+\eta}(ed)}$
-- statement:
--   Fix $\eta>0$ and a multiplier $M\ge1$, and let $W(y)=M\,u(y)A(y)^{2+\eta}$ with $u,A$ as in (12). There are $K\ge1$ and $C,c>0$ (depending on $\eta$ and $M$) such that for every real $d\ge2$, every integer $1\le r\le d$, and independent copies $Y_1,\dots,Y_r$ of $Y$, with $W_i=W(Y_i)$,
--   $$P\Bigl\{\sum_{i=1}^rW_i>Kd\Bigr\}\le C\exp\Bigl[-\frac{cd}{\log^{2+\eta}(ed)}\Bigr].\qquad(17)$$
--
--   In the paper $M=M_\eta$ is the constant of Lemma 3.1. This is the bound that makes a random state balanced for a $d$-sparse normalized vector except with probability $C e^{-cd/\log^{2+\eta}(ed)}$.
--
--   **Formalization Note** The independent copies are realized on the product of $r$ copies of the law of $Y$.
--
--   Differences from the source:
--   - generalization: W = W(Y) of (14) with the constant M_η of Lemma 3.1 → W with any multiplier M ≥ 1; K, C, c depend on (η, M); reason: M_η is existential in Lemma 3.1 and cannot be named; the proof uses only (15), which holds for every M ≥ 1; specializes to M = M_η
--   - generalization: every d ≥ 2, every integer 1 ≤ r ≤ d → d real with d ≥ 2, r a natural number with 1 ≤ r ≤ d; reason: the page calls r, not d, an integer; real d contains every integer d ≥ 2, so the statement specializes to the page's
--   - encoding: independent copies W1, …, Wr of W(Y) → W(y i) under Measure.pi of r copies of rho1 η; reason: the joint law of independent copies is the product law
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.9, Lemma 4.1, eq. (17)

import Mathlib
import Definitions.Def_OnlineBeckFiala_W

open MeasureTheory

namespace OnlineBeckFiala

/-- **Lemma 4.1 (Averaging the coordinate costs), p.9.** Altschuler, Tikhomirov, *Online Beck–Fiala
Down to Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "There are K_η ≥ 1
and C_η, c_η > 0 such that, for every d ≥ 2, every integer 1 ≤ r ≤ d, and independent copies
W1, . . . , Wr of W(Y), P{∑_{i=1}^r Wi > K_η d} ≤ C_η exp[−c_η d / log^{2+η}(ed)]. (17)"

**Formalization Note.** `W = W_M` of (14) with the multiplier `M` a parameter: the lemma is stated for
every `M ≥ 1`, with `K, C, c` depending on `(η, M)`; it specializes to the `M_η` of Lemma 3.1 (whose
`M_η` is existential and cannot be named). Independent copies `W(Y₁), …, W(Y_r)` are realized on the
product law of `r` copies of `rho1 η`. `d` is real, `d ≥ 2`, and `r` is an integer with `1 ≤ r ≤ d`. -/
theorem lemma_4_1 (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ d : ℝ, 2 ≤ d → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ d →
        (Measure.pi (fun _ : Fin r => rho1 η)) {y | K * d < ∑ i, W η M (y i)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η))) := by sorry

end OnlineBeckFiala
