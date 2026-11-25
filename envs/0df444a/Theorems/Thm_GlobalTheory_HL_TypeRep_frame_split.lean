-- Prove2me | Theorems.Thm_GlobalTheory_HL_TypeRep_frame_split
-- name    : GlobalTheory.HL.TypeRep.frame_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:12.578149+00:00
-- url     : https://prove2.me/theorems/cc8793e3-8f5b-59d8-a725-561b7c96b566
-- title:
--   Type Rep: frame split
-- statement:
--   The Type Rep construction uses the frame split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingSecondTypeTestOnRepresentatives.lean#L76-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingSecondTypeTestOnRepresentatives.lean#L76-L104

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.TypeRep.frame_split (Λ : Submodule L.O S.V) (g g' : Fin (r + 1) → S.V) (h0 : S.th ≠ 0)
    (hg : ∀ b, g b ∈ S.spanTo S.f (r + 1))
    (hg' : ∀ b, g' b ∈ Λ ∧ g' b ∈ S.spanTo S.f' (r + 1)) {m : S.V} (hm : m ∈ S.Mof g g') :
    ∃ a ∈ S.spanTo S.f (r + 1), ∃ a' ∈ S.spanTo S.f' (r + 1), a' ∈ Λ ∧
      algebraMap F E S.th • m = a + a' := by sorry
