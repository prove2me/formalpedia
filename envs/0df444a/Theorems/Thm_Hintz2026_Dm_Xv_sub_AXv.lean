-- Prove2me | Theorems.Thm_Hintz2026_Dm_Xv_sub_AXv
-- name    : Hintz2026.Dm_Xv_sub_AXv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:11.093951+00:00
-- url     : https://prove2.me/theorems/d8eb4d98-75a8-4bea-91b8-d394ae5006d9
-- title:
--   Residual identity: D⁻(Xv) - A(Xv) = X · D⁻(v)
-- statement:
--   The key residual identity for the integrating factor $X$: for any differentiable vector field $v$, $D^-(Xv) - A(Xv) = X \cdot D^-v$. Thus $u=Xv$ satisfies $(D^- - A)u=0$ whenever $D^-v=0$. Conversely, the change $v=X^{-1}u$ removes the $-Au$ term from the original homogeneous equation. The displayed residual identity itself is valid without assuming that $v$ solves an equation. The proof uses the product rule for $D^-$ and the integrating factor equation $D^-X = AX$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/Residual.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_Xv_sub_AXv (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = X p x *ᵥ (fun j => Dm p (fun z => v z j) x) := by sorry
