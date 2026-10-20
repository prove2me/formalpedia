-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_X_mulVec
-- name    : Hintz2026.contDiffOn_X_mulVec
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:48:58.963254+00:00
-- url     : https://prove2.me/theorems/37c3c042-c0cc-4672-96d5-92d5ed3efa6b
-- title:
--   X · v is C∞ when v is C∞
-- statement:
--   If each component of $v$ is $C^\infty$ on $U$, then each component of $Xv$ is $C^\infty$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_X_mulVec (p : SubextremalKN) {v : (Fin 2 → ℝ) → Fin 2 → ℂ} (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => (X p x *ᵥ v x) i) (U p) := by sorry
