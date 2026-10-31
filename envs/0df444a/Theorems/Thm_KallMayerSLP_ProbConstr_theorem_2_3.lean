-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_theorem_2_3
-- name    : KallMayerSLP.ProbConstr.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:19.972785+00:00
-- url     : https://prove2.me/theorems/cbd74a11-cfaf-450e-8b92-efef01cb01f3
-- title:
--   Theorem 2.3 (Marti), p.100 — $\mathcal B(\alpha)$ is convex for $\alpha>1-\min_i p_i$
-- statement:
--   Let $\xi$ have the finite discrete distribution given by the realization tableau $(p_i;\hat\xi^i)_{i=1}^N$ with $p_i>0$ and $\sum_i p_i=1$, and let $p_{i_0}=\min_{i\in I}p_i$. Then
--   $$
--   \mathcal B(\alpha)\ \text{is convex for every}\ \alpha>1-p_{i_0}.
--   $$
--
--   For such levels the probability constraint is equivalent to requiring the realized constraints for all realizations, so it defines a convex polyhedron.
--
--   Differences from the source:
--   - generalization: T(ξ), h(ξ) affine in ξ (Notations, p.ix) → T(ξ), h(ξ) arbitrary functions of the realization; reason: only their values at the atoms ξ̂^i enter, and affine data are a special case
--   - encoding: ξ with the finite discrete distribution of the tableau (2.15), indices 1, …, N → τ : RealizationTableau N r with law Σ_i p_i δ_{ξ̂^i}, indices Fin N; reason: the same law; atoms are allowed to coincide, as in the book's tableau
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, Theorem 2.3 (Marti 1971), p.100 (PDF 110)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure

namespace KallMayerSLP.ProbConstr

/-- **Theorem 2.3** (Marti 1971). Let `p_{i₀} = min_{i∈I} p_i`. Then `B(α)` is convex for
`α > 1 − p_{i₀}`.

Kall & Mayer 2005, Chapter 2, Theorem 2.3, p.100 (PDF 110) (proof cited: Kall [134]).

**Formalization Note.** `ξ` has the finite discrete distribution of the realization tableau (2.15)
(`τ.measure = Σ_i p_i · dirac(ξ̂^i)`, `p_i > 0`, `Σ p_i = 1`), indices `Fin N` for `1, …, N`. The data
`T(ξ)`, `h(ξ)` are arbitrary functions of the realization (the book's affine data are a special
case); only their values at the atoms matter. `i₀` is any index attaining the minimum. Every real
`α > 1 − p_{i₀}` (for `α > 1` the set is empty). -/
theorem theorem_2_3 {N r m n : ℕ} (τ : RealizationTableau N r)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (i₀ : Fin N) (hi₀ : ∀ i, τ.p i₀ ≤ τ.p i) (α : ℝ)
    (hα : 1 - τ.p i₀ < α) :
    Convex ℝ (feasibleSet τ.measure T h α) := by sorry

end KallMayerSLP.ProbConstr
