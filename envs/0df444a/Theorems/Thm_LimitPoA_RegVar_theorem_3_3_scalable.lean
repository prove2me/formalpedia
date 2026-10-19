-- Prove2me | Theorems.Thm_LimitPoA_RegVar_theorem_3_3_scalable
-- name    : LimitPoA.RegVar.theorem_3_3_scalable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:33.837261+00:00
-- url     : https://prove2.me/theorems/98319fe6-f317-4d6a-902f-094b95bc306f
-- title:
--   Theorem 3.3, p. 23, first clause — games with regularly varying cost functions are scalable by decomposition
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, whose cost functions $\tau_a$ are non-negative, non-decreasing and continuous on $[0,\infty)$ and regularly varying, each with its own regular variation index. Then $\Gamma$ is scalable by decomposition: every regular sequence $(d^{(n)})$ has an infinite subsequence $(n_i)$ such that $(d^{(n_i)}_{|\mathcal K_{reg}})_i$ is decomposable and
--   $$\Gamma_{|\mathcal K_{reg}} \asymp_{d^{(n_i)}_{|\mathcal K_{reg}}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$$
--   for non-empty classes $\mathcal K_1,\dots,\mathcal K_m$ partitioning $\mathcal K_{reg}$.
--
--   This is the step of the main theorem that uses regular variation: it supplies, for every class, a scaling sequence and a limit game.
--
--   **Formalization Note** Regular variation is the definition of §1.2, p. 6, applied to each $\tau_a$ separately; no common index is assumed.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 23, Theorem 3.3, first clause (proof Appendix A.5, pp. 43–44)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

/-- Theorem 3.3, p. 23, first clause: games with regularly varying cost functions are scalable by
decomposition. -/
theorem theorem_3_3_scalable (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a)) :
    IsScalableByDecomposition Γ τ := by sorry

end LimitPoA.RegVar
