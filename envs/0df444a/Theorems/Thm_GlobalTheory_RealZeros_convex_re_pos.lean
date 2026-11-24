-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_convex_re_pos
-- name    : GlobalTheory.RealZeros.convex_re_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:40.36805+00:00
-- url     : https://prove2.me/theorems/6610d84d-e1e4-4b55-86c9-45df0db76bb6
-- title:
--   Real Zeros: convex re pos
-- statement:
--   The Real Zeros construction uses the convex re pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L95-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L95-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros

theorem GlobalTheory.RealZeros.convex_re_pos : Convex ℝ {s : ℂ | 0 < s.re} := by sorry
