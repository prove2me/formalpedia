-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_Xstar_entry
-- name    : Hintz2026.contDiffOn_Xstar_entry
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:12.180549+00:00
-- url     : https://prove2.me/theorems/4d305805-23b3-45cd-9f2c-1f0dc78e94b1
-- title:
--   Matrix entries of X* are C∞ on U
-- statement:
--   Each entry of the conjugate transpose $X^*$ is $C^\infty$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_Xstar_entry (p : SubextremalKN) (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => (X p x)ᴴ i j) (U p) := by sorry
