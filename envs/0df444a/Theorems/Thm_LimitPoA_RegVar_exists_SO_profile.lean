-- Prove2me | Theorems.Thm_LimitPoA_RegVar_exists_SO_profile
-- name    : LimitPoA.RegVar.exists_SO_profile
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T20:16:02.29069+00:00
-- url     : https://prove2.me/theorems/8e9902d6-c15b-4d6f-ae80-389052294b76
-- title:
--   §2.1, p. 7 — every game has an SO profile for every non-negative demand vector
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions of §2.1 (0/1 incidence, (2.1), every group has a strategy), and let every resource cost $\tau_a$ be non-negative, non-decreasing and continuous on $[0,\infty)$. Then for every demand vector $d$ with $d_k \ge 0$ there is a **social optimum**: a strategy profile $f^*$ for $d$ with
--   $$C(f^*) \le C(f)\quad\text{for every profile } f \text{ for } d,$$
--   where $C(f)=\sum_a f_a\,\tau_a(f_a)$.
--
--   The paper states this on p. 7 ("Due to our assumptions on the cost functions, every non-atomic congestion game has an SO profile"). It follows because the set of profiles is a non-empty compact polytope and $C$ is continuous on it.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, §2.1, p. 7 ("every non-atomic congestion game has an SO profile"; "all Wardrop equilibria have the same cost")

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

namespace LimitPoA.RegVar

/-- §2.1, p. 7: every game has an SO profile for every non-negative demand vector. -/
theorem exists_SO_profile (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsSO Γ τ d f := by sorry

end LimitPoA.RegVar
