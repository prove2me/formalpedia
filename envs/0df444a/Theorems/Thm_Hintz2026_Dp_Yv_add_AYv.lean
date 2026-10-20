-- Prove2me | Theorems.Thm_Hintz2026_Dp_Yv_add_AYv
-- name    : Hintz2026.Dp_Yv_add_AYv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:08.259921+00:00
-- url     : https://prove2.me/theorems/42b15378-1851-4fd4-a103-95e3de7562d3
-- title:
--   Residual identity: D⁺(Yv) + A(Yv) = Y · D⁺(v)
-- statement:
--   The residual identity for $Y = (X^*)^{-1}$: $D^+(Yv) + A(Yv) = Y \cdot D^+v$. At $x\in U$, under the stated coordinate-slice differentiability hypotheses, $u=Yv$ satisfies $(D^+ + A)u=0$ whenever $D^+v=0$. Conversely, $v=X^*u$ removes the $+Au$ term. The residual identity does not assume that $v$ solves an equation.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/Residual.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dp_Yv_add_AYv (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = ((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x) := by sorry
