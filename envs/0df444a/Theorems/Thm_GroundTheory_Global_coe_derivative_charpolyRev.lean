-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_derivative_charpolyRev
-- name    : GroundTheory.Global.coe_derivative_charpolyRev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:47.825377+00:00
-- url     : https://prove2.me/theorems/e3951d16-af31-42a0-8059-4f53eccd20d8
-- title:
--   Global: coe derivative charpoly Rev
-- statement:
--   The Global construction uses the coe derivative charpoly Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L51-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L51-L88

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

theorem GroundTheory.Global.coe_derivative_charpolyRev (M : Matrix n n R) :
    ((derivative M.charpolyRev : R[X]) : PowerSeries R) =
      -(M.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by sorry
