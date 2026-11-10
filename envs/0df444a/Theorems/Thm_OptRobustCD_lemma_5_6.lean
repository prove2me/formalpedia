-- Prove2me | Theorems.Thm_OptRobustCD_lemma_5_6
-- name    : OptRobustCD.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:39.20737+00:00
-- url     : https://prove2.me/theorems/775e05ac-b73f-4d96-8176-f4e10caedbab
-- title:
--   Lemma 5.6 — informative negative eigenvector: $M_s$ has exactly one negative eigenvalue, $\sigma^{(s)}$ is nearly its eigenvector and is delocalized
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and $M_s$ the corrected Bethe Hessian of Definition 5.5 with the constant $L$ large enough. There is a constant $g(d,\lambda)>0$ such that for every $\varepsilon>0$ there is $s_0(\varepsilon)$ such that for every $s>s_0$, with high probability $M_s$ has exactly one negative eigenvalue and
--   $$\|(M_s+gI)\sigma^{(s)}\|\le\varepsilon\|\sigma^{(s)}\|.$$
--   Moreover, there is $C=C(d,\lambda)$, not depending on $s$, such that with high probability
--   $$\frac{\|\sigma^{(s)}\|_4^4}{\|\sigma^{(s)}\|^4}\le\frac Cn.$$
--
--   It reduces the problem to recovering a delocalized negative eigenvector robustly (Lemma 5.9).
--
--   Differences from the source:
--   - reading: L = L(d,λ) ⩾ 2 a sufficiently large constant (Definition 5.5) → ∃ L₀ ⩾ 2, ∀ L ⩾ L₀; reason: the meaning of 'sufficiently large'
--   - encoding: number of negative eigenvalues → negative real roots of the characteristic polynomial with multiplicity; reason: equal for real symmetric matrices, which M_s and H are
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: quotients the source writes only where they are defined → Lean's x/0 = 0 at a zero denominator; reason: changes no instance where the source's quotient is defined; on the high-probability event the denominators are nonzero
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 5.6, p.26 (pdf p.28); restated p.28 (pdf p.30)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BetheHessian
import Definitions.Def_OptRobustCD_RowNorms

namespace OptRobustCD

/-- **Lemma 5.6** (Informative negative eigenvector). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 5.6, p.26 (pdf p.28; restated p.28, pdf p.30).

"Let dλ² > 1. There is a constant g(d, λ) > 0 such that for every ε > 0 there is `s_0(ε)` such that
for every `s > s_0`, with high probability `M_s` has exactly one negative eigenvalue, and `σ^{(s)}`
is approximately an associated eigenvector, in that `∥(M_s + gI)σ^{(s)}∥ ⩽ ε∥σ^{(s)}∥`. Moreover,
there is C = C(d, λ), not depending on s, such that with high probability, `σ^{(s)}` is
delocalized, in that `∥σ^{(s)}∥⁴_4/∥σ^{(s)}∥⁴ ⩽ C/n`."

**Formalization Note.** `M_s` depends on the constant `L` of Definition 5.5, "sufficiently large":
the statement holds for every `L ⩾ L₀` for some `L₀ ⩾ 2`. "Exactly one negative eigenvalue" counts
with multiplicity. `s > s₀` is strict, as printed. `d > 0`, `λ ∈ (−1, 1)` and the SBM are the
standing assumptions of §3.1. -/
theorem lemma_5_6 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    ∃ L₀ : ℕ, 2 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      (∃ g : ℝ, 0 < g ∧ ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℕ, ∀ s : ℕ, s₀ < s → Whp d lam (fun _n σ G =>
        negCount (Ms d lam L s G) = 1 ∧
        l2 ((Ms d lam L s G + g • (1 : Matrix _ _ ℝ)).mulVec (sigmaS d lam s G σ)) ≤
          ε * l2 (sigmaS d lam s G σ))) ∧
      (∃ C : ℝ, ∀ s : ℕ, Whp d lam (fun n σ G =>
        l4pow4 (sigmaS d lam s G σ) / l2 (sigmaS d lam s G σ) ^ 4 ≤ C / n)) := by sorry

end OptRobustCD
