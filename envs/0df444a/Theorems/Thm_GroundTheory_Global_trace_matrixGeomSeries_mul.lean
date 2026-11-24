-- Prove2me | Theorems.Thm_GroundTheory_Global_trace_matrixGeomSeries_mul
-- name    : GroundTheory.Global.trace_matrixGeomSeries_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:06.896248+00:00
-- url     : https://prove2.me/theorems/e5bdf9f7-d0b2-43b7-9b0c-e5c555494f39
-- title:
--   Global: trace matrix Geom Series mul
-- statement:
--   The Global construction uses the trace matrix Geom Series mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L32-L40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem GroundTheory.Global.trace_matrixGeomSeries_mul (M : Matrix n n R) :
    (matrixGeomSeries M * M.map PowerSeries.C).trace =
      PowerSeries.mk fun k => (M ^ (k + 1)).trace := by sorry
