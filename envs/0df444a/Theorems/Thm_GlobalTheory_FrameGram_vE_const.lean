-- Prove2me | Theorems.Thm_GlobalTheory_FrameGram_vE_const
-- name    : GlobalTheory.FrameGram.vE_const
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:45.99903+00:00
-- url     : https://prove2.me/theorems/55782aa5-96df-4437-b1f2-d07f87e23ed5
-- title:
--   Frame Gram: v E const
-- statement:
--   The Frame Gram construction uses the v E const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L108-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L108-L139

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameGram.vE_const [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (c : F) (hc : c ≠ 0) (m : ℕ) :
    vE L S.ϖ (algebraMap F E ((-1) ^ (r + 1) * c * S.th⁻¹ ^ m)) =
      vE L S.ϖ (algebraMap F E c) - m * S.vth := by sorry
