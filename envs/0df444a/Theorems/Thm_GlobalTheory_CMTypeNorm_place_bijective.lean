-- Prove2me | Theorems.Thm_GlobalTheory_CMTypeNorm_place_bijective
-- name    : GlobalTheory.CMTypeNorm.place_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:49.631851+00:00
-- url     : https://prove2.me/theorems/62fd1dde-6686-493d-9cdb-85289aad4190
-- title:
--   CMType Norm: place bijective
-- statement:
--   The CMType Norm construction uses the place bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypeProdNormSqEqAbsNormSpan.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypeProdNormSqEqAbsNormSpan.lean#L11-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.CMTypeNorm

theorem GlobalTheory.CMTypeNorm.place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by sorry
