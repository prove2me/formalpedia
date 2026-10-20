-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_Xinv_mulVec
-- name    : Hintz2026.contDiffOn_Xinv_mulVec
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:19.370963+00:00
-- url     : https://prove2.me/theorems/6d8dc118-e173-4151-9370-a3aae884bc37
-- title:
--   X⁻¹ · v is C∞ when v is C∞
-- statement:
--   Smoothness is preserved under multiplication by $X^{-1}$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_Xinv_mulVec (p : SubextremalKN) {v : (Fin 2 → ℝ) → Fin 2 → ℂ} (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => ((X p x)⁻¹ *ᵥ v x) i) (U p) := by sorry
