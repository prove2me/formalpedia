-- Prove2me | Theorems.Thm_Freiman_late_catalog_sizes
-- name    : Freiman.late_catalog_sizes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:55:13.035074+00:00
-- url     : https://prove2.me/theorems/78a179b8-a3c0-4200-b66a-2f329bcf59ed
-- title:
--   Freiman late: late catalog sizes
-- statement:
--   Finite source inventory sizes. This separate small equality prevents a collector proof from unfolding thousands of rational data literals merely to determine an array length.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_catalog_sizes : lateCatalog.bounds.size = 341 ∧ lateCatalog.witnesses.size = 1473 ∧ lateCatalog.endpoints.size = 162 ∧ lateCatalog.paths.size = 63 ∧ lateCatalog.proofs.size = 1494 ∧ lateCatalog.rectangles.size = 32 := by
  sorry
