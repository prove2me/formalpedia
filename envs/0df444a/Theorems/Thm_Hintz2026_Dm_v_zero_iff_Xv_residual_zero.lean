-- Prove2me | Theorems.Thm_Hintz2026_Dm_v_zero_iff_Xv_residual_zero
-- name    : Hintz2026.Dm_v_zero_iff_Xv_residual_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:02.517433+00:00
-- url     : https://prove2.me/theorems/4b89a002-488e-4146-a09e-34ff66cda989
-- title:
--   D⁻v=0 iff D⁻(Xv)-A(Xv)=0 (pointwise)
-- statement:
--   Pointwise equivalence: $D^-v = 0$ if and only if $D^-(Xv) - A(Xv) = 0$, for differentiable $v$ at a point of $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/SolutionCorr.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_v_zero_iff_Xv_residual_zero (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun j => Dm p (fun z => v z j) x) = 0 ↔ (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = 0 := by sorry
