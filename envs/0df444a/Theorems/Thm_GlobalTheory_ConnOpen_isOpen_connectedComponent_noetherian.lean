-- Prove2me | Theorems.Thm_GlobalTheory_ConnOpen_isOpen_connectedComponent_noetherian
-- name    : GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:31.519777+00:00
-- url     : https://prove2.me/theorems/472a36d6-73d7-41ff-b0d1-55b52fc6246c
-- title:
--   Conn Open: is Open connected Component noetherian
-- statement:
--   The Conn Open construction uses the is Open connected Component noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherian.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherian.lean#L10-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConnOpen

theorem GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by sorry
