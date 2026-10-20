-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_A_entry
-- name    : Hintz2026.contDiffOn_A_entry
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:05.857739+00:00
-- url     : https://prove2.me/theorems/d3ce956e-2259-4a01-b96e-19478cb7d639
-- title:
--   Matrix entries of A are C∞ on U
-- statement:
--   Each entry of the coefficient matrix $A$ is $C^\infty$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/Smooth.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_A_entry (p : SubextremalKN) (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => A p x i j) (U p) := by sorry
