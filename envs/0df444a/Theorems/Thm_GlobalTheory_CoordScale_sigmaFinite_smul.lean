-- Prove2me | Theorems.Thm_GlobalTheory_CoordScale_sigmaFinite_smul
-- name    : GlobalTheory.CoordScale.sigmaFinite_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:42.603456+00:00
-- url     : https://prove2.me/theorems/10f86cca-a800-4cbe-bbb1-7f7088a042da
-- title:
--   Coord Scale: sigma Finite smul
-- statement:
--   The Coord Scale construction uses the sigma Finite smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory

theorem GlobalTheory.CoordScale.sigmaFinite_smul {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by sorry
