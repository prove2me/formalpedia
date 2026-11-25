-- Prove2me | Theorems.Thm_GlobalTheory_FrameGram_lead_mul_upper
-- name    : GlobalTheory.FrameGram.lead_mul_upper
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:47.034425+00:00
-- url     : https://prove2.me/theorems/d1416a3f-384c-4b00-b5c4-a2b8e81b9964
-- title:
--   Frame Gram: lead mul upper
-- statement:
--   The Frame Gram construction uses the lead mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L39-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram

theorem GlobalTheory.FrameGram.lead_mul_upper {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (M * B) l = lead M l := by sorry
