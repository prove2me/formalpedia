-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_eq_2_20
-- name    : KallMayerSLP.ProbConstr.eq_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:28.320412+00:00
-- url     : https://prove2.me/theorems/df57d683-2871-431e-b4ba-ea0d4fb4a107
-- title:
--   p.100 and (2.20) — $\alpha>1-p_{i_0}$ gives $\mathcal B(\alpha)=\mathcal B(1)=\bigcap_i K_i$ (corrected: $\alpha\le1$)
-- statement:
--   Let $\xi$ have the finite discrete distribution given by the realization tableau $(p_i;\hat\xi^i)_{i=1}^N$ with $p_i>0$ and $\sum_i p_i=1$, and let $p_{i_0}=\min_{i\in I}p_i$. If $1-p_{i_0}<\alpha\le1$, then
--   $$
--   \mathcal B(\alpha)=\mathcal B(1)\qquad\text{and}\qquad \mathcal B(1)=\{x\mid T(\hat\xi^i)x\ge h(\hat\xi^i),\ i=1,\dots,N\}=\bigcap_{i=1}^N K_i .
--   $$
--   Consequently the probability constraint can be replaced by the system of linear inequalities (2.20), which asks for a "fat solution".
--
--   Differences from the source:
--   - correction: α > 1 − p_{i₀} implies B(α) = B(1) → the hypotheses 1 − p_{i₀} < α and α ≤ 1; reason: for α > 1 the printed implication is false: N = 1, p_1 = 1, T = 0, h = 0, α = 2 give B(2) = ∅ while B(1) = ℝ^n
--   - generalization: T(ξ), h(ξ) affine in ξ (Notations, p.ix) → T(ξ), h(ξ) arbitrary functions of the realization; reason: only their values at the atoms ξ̂^i enter, and affine data are a special case
--   - encoding: ξ with the finite discrete distribution of the tableau (2.15), indices 1, …, N → τ : RealizationTableau N r with law Σ_i p_i δ_{ξ̂^i}, indices Fin N; reason: the same law; atoms are allowed to coincide, as in the book's tableau
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, remark after Theorem 2.3 and (2.20), p.100 (PDF 110)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure

namespace KallMayerSLP.ProbConstr

/-- The remark after Theorem 2.3: if `p_{i₀} = min_{i∈I} p_i`, then `α > 1 − p_{i₀}` implies
`B(α) = B(1)`; consequently the probability constraint can be replaced by the system of linear
inequalities (2.20) `T(ξ̂^i)x ≥ h(ξ̂^i)`, `i = 1, …, N`, i.e. `B(1) = ⋂_i K_i`.

Kall & Mayer 2005, Chapter 2, the paragraph after Theorem 2.3 and (2.20), p.100 (PDF 110).

**Formalization Note.** `ξ` has the finite discrete distribution of the realization tableau (2.15)
(`τ.measure = Σ_i p_i · dirac(ξ̂^i)`, `p_i > 0`, `Σ p_i = 1`), indices `Fin N` for `1, …, N`. The data
`T(ξ)`, `h(ξ)` are arbitrary functions of the realization (the book's affine data are a special
case); only their values at the atoms matter. The level is restricted to `α ≤ 1` (a probability level):
for `α > 1` the printed implication fails, since `B(α) = ∅` while `B(1) = ⋂_i K_i` may be nonempty
(e.g. `N = 1`, `T = 0`, `h = 0`, `α = 2`: `B(2) = ∅`, `B(1) = ℝ^n`). -/
theorem eq_2_20 {N r m n : ℕ} (τ : RealizationTableau N r)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (i₀ : Fin N) (hi₀ : ∀ i, τ.p i₀ ≤ τ.p i) (α : ℝ)
    (hα : 1 - τ.p i₀ < α) (hα₁ : α ≤ 1) :
    feasibleSet τ.measure T h α = feasibleSet τ.measure T h 1 ∧
      feasibleSet τ.measure T h 1 = ⋂ i, realizationSet T h (τ.xi i) := by sorry

end KallMayerSLP.ProbConstr
