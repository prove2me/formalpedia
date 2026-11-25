-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameChange_sum_mem_spanTo
-- name    : GlobalTheory.HL.FrameChange.sum_mem_spanTo
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:33:32.122628+00:00
-- url     : https://prove2.me/theorems/d9e5644b-24bc-564a-82b1-28246a45729a
-- title:
--   Frame Change: sum mem span To
-- statement:
--   The Frame Change construction uses the sum mem span To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFramesCongrModThetaUnitriangular.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFramesCongrModThetaUnitriangular.lean#L36-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFramesCongrModThetaUnitriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameChange
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.FrameChange.sum_mem_spanTo (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j := by sorry
