-- Prove2me | Theorems.Thm_LimitPoA_RegVar_corollary_3_2
-- name    : LimitPoA.RegVar.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:32.079681+00:00
-- url     : https://prove2.me/theorems/b82426a8-4d9c-446c-82f4-419c5c841467
-- title:
--   Corollary 3.2, p. 23 — games that are scalable by decomposition are asymptotically well designed
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$. If $\Gamma$ is scalable by decomposition (Definition 3.6), then $\Gamma$ is asymptotically well designed: for every unbounded demand sequence $(d^{(n)})_{n\in\mathbb N}$,
--   $$\lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = 1.$$
--
--   Together with the first clause of Theorem 3.3 it yields the paper's main result.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 23, Corollary 3.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

/-- Corollary 3.2, p. 23: games that are scalable by decomposition are asymptotically well designed. -/
theorem corollary_3_2 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (hsd : IsScalableByDecomposition Γ τ) :
    IsAsymptoticallyWellDesigned Γ τ := by sorry

end LimitPoA.RegVar
