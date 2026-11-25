-- Prove2me | Theorems.Thm_GlobalTheory_CoordScale_pi_smul_ne_top
-- name    : GlobalTheory.CoordScale.pi_smul_ne_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:06.224882+00:00
-- url     : https://prove2.me/theorems/22bcbce6-06a3-5e0b-9c25-9d688a6eb917
-- title:
--   Coord Scale: pi smul ne top
-- statement:
--   The Coord Scale construction uses the pi smul ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L13-L18

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

theorem GlobalTheory.CoordScale.pi_smul_ne_top {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by sorry
