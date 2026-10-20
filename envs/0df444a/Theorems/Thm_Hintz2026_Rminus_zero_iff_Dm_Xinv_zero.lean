-- Prove2me | Theorems.Thm_Hintz2026_Rminus_zero_iff_Dm_Xinv_zero
-- name    : Hintz2026.Rminus_zero_iff_Dm_Xinv_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:11.19308+00:00
-- url     : https://prove2.me/theorems/ca35314d-1445-4024-af0f-5fe45daafbe9
-- title:
--   D⁻(X⁻¹u)=0 iff D⁻u - Au=0
-- statement:
--   Reverse equivalence: $D^-(X^{-1}u) = 0$ iff $D^-u - Au = 0$, for $C^\infty$ fields $u$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Rminus_zero_iff_Dm_Xinv_zero (p : SubextremalKN) (u : (Fin 2 → ℝ) → Fin 2 → ℂ) (hu : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => u x j) (U p)) {x : Fin 2 → ℝ} (hx : x ∈ U p) : (fun j => Dm p (fun z => ((X p z)⁻¹ *ᵥ u z) j) x) = 0 ↔ (fun i => Dm p (fun z => u z i) x) - A p x *ᵥ u x = 0 := by sorry
