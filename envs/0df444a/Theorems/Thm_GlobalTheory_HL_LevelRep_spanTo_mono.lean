-- Prove2me | Theorems.Thm_GlobalTheory_HL_LevelRep_spanTo_mono
-- name    : GlobalTheory.HL.LevelRep.spanTo_mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:33.965265+00:00
-- url     : https://prove2.me/theorems/6cf54ed8-124e-41e4-bf9b-50181b4d37da
-- title:
--   Level Rep: span To mono
-- statement:
--   The Level Rep construction uses the span To mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermLevelZeroAndBoundedRepresentatives.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermLevelZeroAndBoundedRepresentatives.lean#L52-L53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentatives
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LevelRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable {S} {g g' : Fin (r + 1) → S.V}

theorem GlobalTheory.HL.LevelRep.spanTo_mono (g : Fin (r + 1) → S.V) {j j' : ℕ} (h : j ≤ j') : S.spanTo g j ≤ S.spanTo g j' := by sorry
