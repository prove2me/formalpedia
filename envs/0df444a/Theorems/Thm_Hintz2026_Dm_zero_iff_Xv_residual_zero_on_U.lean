-- Prove2me | Theorems.Thm_Hintz2026_Dm_zero_iff_Xv_residual_zero_on_U
-- name    : Hintz2026.Dm_zero_iff_Xv_residual_zero_on_U
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:20.249305+00:00
-- url     : https://prove2.me/theorems/45ba49cf-e5be-4df1-aab0-d26612a4b81a
-- title:
--   D⁻v=0 on U iff Xv residual=0 on U (C∞ fields)
-- statement:
--   For $C^\infty$ vector fields $v$ on $U$: $D^-v = 0$ pointwise on $U$ if and only if the $X$-transformed residual $D^-(Xv) - A(Xv) = 0$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_zero_iff_Xv_residual_zero_on_U (p : SubextremalKN) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) : (∀ x ∈ U p, (fun j => Dm p (fun z => v z j) x) = 0) ↔ (∀ x ∈ U p, (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = 0) := by sorry
