-- Prove2me | Theorems.Thm_LuoSunLiu_PLBLower_two_point_construction
-- name    : LuoSunLiu.PLBLower.two_point_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:57.338071+00:00
-- url     : https://prove2.me/theorems/1e1f54f2-f574-49da-80fe-4c087e1636f0
-- title:
--   Proof of Proposition 2, p. 44 — ξ_u, ξ_v ∈ PB(ξ̃, C_p) and ⟨ξ_u,U⟩ = (u−C)/(u+C) ≤ 1 = ⟨ξ_v,U⟩, ⟨ξ_v,V⟩ = (v−C)/(v+C) ≤ 1 = ⟨ξ_u,V⟩
-- statement:
--   Let $\tilde\xi\in\mathbb R^d$ have positive entries, let $j_u\neq j_v$ be two coordinates with $u=\tilde\xi_{j_u}$, $v=\tilde\xi_{j_v}$, and let $C$ satisfy $0\le C<u$ and $C<v$. Let $U,V,\xi_u,\xi_v$ be the two actions and two parameters of the two-point construction, and $C_p=2C$. Then
--
--   1. $\xi_u\in PB(\tilde\xi,C_p)$ and $\xi_v\in PB(\tilde\xi,C_p)$, i.e. $\|\xi_u-\tilde\xi\|_\infty\le C$ and $\|\xi_v-\tilde\xi\|_\infty\le C$;
--   2. the inner products are
--   $$\langle\xi_u,U\rangle=\frac{u-C}{u+C}\le1=\langle\xi_v,U\rangle,\qquad \langle\xi_v,V\rangle=\frac{v-C}{v+C}\le1=\langle\xi_u,V\rangle.$$
--
--   So under $\xi_u$ the action $V$ is optimal and $U$ loses $2C/(u+C)$; under $\xi_v$ the action $U$ is optimal and $V$ loses $2C/(v+C)$. This is the first step of the proof of the $\Omega(C_pT_0)$ lower bound.
--
--   **Formalization Note** The statement is written with $C$ and $C_p=2C$. It holds for any two distinct coordinates; the paper's choice of the smallest and second smallest entries is only needed in the per-period bound. The hypothesis $0\le C$ is the paper's implicit nonnegativity of the perturbation constant.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, App. A, proof of Proposition 2, p. 44

import Mathlib
import Definitions.Def_LuoSunLiu_PLBLower_Model
import Definitions.Def_LuoSunLiu_PLBLower_TwoPoint

namespace LuoSunLiu.PLBLower

/-- Two-point construction (proof of Proposition 2, p. 44). With `C = C_p / 2`, i.e. `C_p = 2C`:
`ξ_u, ξ_v ∈ PB(ξ̃, C_p)`, `⟨ξ_u, U⟩ = (u − C)/(u + C) ≤ 1 = ⟨ξ_v, U⟩` and
`⟨ξ_v, V⟩ = (v − C)/(v + C) ≤ 1 = ⟨ξ_u, V⟩`, where `u = ξ̃_{ju}`, `v = ξ̃_{jv}`. -/
theorem two_point_construction {d : ℕ} (ξc : Fin d → ℝ) (hpos : ∀ i, 0 < ξc i)
    (C : ℝ) (hC0 : 0 ≤ C) (ju jv : Fin d) (hne : ju ≠ jv)
    (hCu : C < ξc ju) (hCv : C < ξc jv) :
    xiU ξc C ju jv ∈ PB ξc (2 * C) ∧ xiV ξc C ju jv ∈ PB ξc (2 * C) ∧
    xiU ξc C ju jv ⬝ᵥ actU ξc C ju = (ξc ju - C) / (ξc ju + C) ∧
    (ξc ju - C) / (ξc ju + C) ≤ 1 ∧
    xiV ξc C ju jv ⬝ᵥ actU ξc C ju = 1 ∧
    xiV ξc C ju jv ⬝ᵥ actV ξc C jv = (ξc jv - C) / (ξc jv + C) ∧
    (ξc jv - C) / (ξc jv + C) ≤ 1 ∧
    xiU ξc C ju jv ⬝ᵥ actV ξc C jv = 1 := by sorry

end LuoSunLiu.PLBLower
