-- Prove2me | Theorems.Thm_Hintz2026_Dp_v_zero_iff_Yv_residual_zero
-- name    : Hintz2026.Dp_v_zero_iff_Yv_residual_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:08.1168+00:00
-- url     : https://prove2.me/theorems/153492d6-26f6-4b41-a248-82812a8f444c
-- title:
--   D⁺v=0 iff D⁺(Yv)+A(Yv)=0 (pointwise)
-- statement:
--   Pointwise equivalence: $D^+v = 0$ if and only if $D^+(Yv) + A(Yv) = 0$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/SolutionCorr.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dp_v_zero_iff_Yv_residual_zero (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun j => Dp p (fun z => v z j) x) = 0 ↔ (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = 0 := by sorry
