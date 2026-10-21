-- Prove2me | Theorems.Thm_LimitPoA_RegVar_NE_cost_unique
-- name    : LimitPoA.RegVar.NE_cost_unique
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T20:16:12.071712+00:00
-- url     : https://prove2.me/theorems/799d8d9a-aeab-4dee-b1be-06f0f1acdd7c
-- title:
--   §2.1, p. 7 — all NE profiles (Wardrop equilibria) for the same demand have the same social cost
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions of §2.1, with resource costs $\tau_a$ non-negative, non-decreasing and continuous on $[0,\infty)$. If $\tilde f$ and $\tilde f'$ are both NE profiles (Wardrop equilibria) for the same demand vector $d$, then
--   $$C(\tilde f) = C(\tilde f').$$
--
--   The paper states on p. 7 that Wardrop equilibria have the same resource costs $\tau_a(\tilde f_a)=\tau_a(\tilde f'_a)$ and hence the same social cost (citing Smith 1979 and Roughgarden–Tardos). This is what makes $\mathrm{PoA}(d)$ independent of the chosen NE profile.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, §2.1, p. 7 ("every non-atomic congestion game has an SO profile"; "all Wardrop equilibria have the same cost")

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

namespace LimitPoA.RegVar

/-- §2.1, p. 7: all NE profiles (Wardrop equilibria) for the same demand vector have the same
social cost. -/
theorem NE_cost_unique (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (f f' : Fin Γ.R → ℝ)
    (hf : IsNE Γ τ d f) (hf' : IsNE Γ τ d f') : cost Γ τ f = cost Γ τ f' := by sorry

end LimitPoA.RegVar
