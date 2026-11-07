-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_4_5
-- name    : OWFLocalDesc.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:51:00.571697+00:00
-- url     : https://prove2.me/theorems/a44c4f2c-02c2-4fe7-aaac-5458f3a2aee5
-- title:
--   Theorem 4.5 (Uniform-data hardness from one-way functions)
-- statement:
--   Assume one-way functions exist. Fix a decoder $U$ and a full-anchor lookup program $\sigma_L$, a polynomially bounded, polynomial-time computable schedule $m(n)\ge 8n$, constants $0<\theta_1\le\theta_2\le1$ and an integer $a\ge0$. Then there are polynomials $t_0(n)$ and $p(n)\ge1$ such that for every polynomial query clock $t\ge t_0$:
--
--   1. $t$ permits full-anchor lookup, and
--   2. every PPT algorithm $B$ eventually satisfies
--   $$\Pr_{(X,Y)\sim D_{0,n},\,B}\Big[\mathrm{pSC}^t_{\theta_1}(X,Y)-a\lceil\log m(n)\rceil\ \le\ B(1^n,X,Y)\ \le\ \mathrm{pSC}^t_{\theta_2}(X,Y)+a\lceil\log m(n)\rceil\Big]\ <\ 1-\frac{1}{p(n)},$$
--   where $D_{0,n}$ draws $m(n)$ independent uniform $n$-bit points and $m(n)$ independent uniform labels.
--
--   This is the hard half of the paper's characterization: if one-way functions exist, no efficient algorithm estimates the shortest local certificate of random labeled data, even within a window between two quantiles and with logarithmic additive slack. The polynomials $t_0$ and $p$ are chosen before the clock and the algorithm.
--
--   **Formalization Note** "Eventually" means: for each $B$ there is $n_0$ such that the bound holds for all $n\ge n_0$.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the fixed full-anchor lookup program (p.13) → every lookup program σL with `IsLookupHeader` (correct whenever it halts, halts within a polynomial in the lengths of anchor list and query); reason: the paper fixes the program without naming it; the result is meant for any such choice, and the polynomial halting bound is the running time stated on p.13
--   - encoding: polynomial schedules (m, t ≥ 1) and positive polynomials p(n) ≥ 1, t₀(n), t_D(n) → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; existential or universal polynomials in ℕ[X] with values ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a PPT algorithm receiving 1^n and a dataset, whose output is a binary integer or the symbol ∞ (else a failure) → `PPT`: one `CookPvsNP.PolyTimeComputable` machine on the code of (coins, input), coin count polynomial in the input length; input `datasetCode`; output read by `decodeOut`; reason: the standard uniform PPT model with fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.5, p.19 (restatement of Theorem 1.1)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_succUniform
import Definitions.Def_OWFLocalDesc_IsLookupHeader
import Definitions.Def_OWFLocalDesc_PermitsLookup
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 4.5 (Uniform-data hardness; restatement of Theorem 1.1).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Theorem 4.5, p.19: "Assume one-way functions exist. Fix a polynomially bounded, polynomial-time
computable integer schedule m(n) ≥ 8n. Fix constants 0 < θ1 ≤ θ2 ≤ 1 and an integer a ≥ 0. There are
polynomials t0(n) and p(n) ≥ 1 such that, for every polynomial query clock t ≥ t0, every PPT
algorithm B eventually satisfies Pr_{(X,Y)∼D_{0,n},B}[pSC^t_{θ1}(X,Y) − a⌈log m(n)⌉ ≤ B(1^n,X,Y)
≤ pSC^t_{θ2}(X,Y) + a⌈log m(n)⌉] < 1 − 1/p(n). Every such clock t permits the full-anchor lookup
procedure on U."

**Formalization Note.** For every decoder `U` and every full-anchor lookup header `σL` ("the"
lookup program of p.13). Schedules are `QuantumPRC.EffPoly` with the standing `m, t ≥ 1` (§2.1,
p.12); `t₀` and `p` are polynomials with natural coefficients, chosen before `t` and `B`;
"eventually" is `∃ n₀, ∀ n ≥ n₀` with `n₀` after `B`. `⌈log m⌉` is `Nat.clog 2 m`. -/
theorem theorem_4_5 (hOWF : OWFExist) (U : Decoder) (σL : List Bool) (hσL : IsLookupHeader U σL)
    (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m) (hm1 : ∀ n, 1 ≤ m n) (hm8 : ∀ n, 8 * n ≤ m n)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₁₂ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ 1) (a : ℕ) :
    ∃ t₀ p : Polynomial ℕ, (∀ n, 1 ≤ p.eval n) ∧
      ∀ t : ℕ → ℕ, QuantumPRC.EffPoly t → (∀ n, 1 ≤ t n) → (∀ n, t₀.eval n ≤ t n) →
        PermitsLookup U σL m t ∧
        ∀ B : PPT, ∃ n₀ : ℕ, ∀ n ≥ n₀,
          succUniform U t m θ₁ θ₂ (a * Nat.clog 2 (m n)) B n < 1 - 1 / ((p.eval n : ℕ) : ℝ) := by sorry

end OWFLocalDesc
