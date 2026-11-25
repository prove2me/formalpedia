-- Prove2me | Theorems.Thm_GlobalTheory_HL_DivisibleGauss_index_span_involution
-- name    : GlobalTheory.HL.DivisibleGauss.index_span_involution
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:44.644682+00:00
-- url     : https://prove2.me/theorems/3157810d-88ee-4b89-b51e-5fde5cb763d5
-- title:
--   Divisible Gauss: index span involution
-- statement:
--   The Divisible Gauss construction uses the index span involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLocalCharacterSum.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLocalCharacterSum.lean#L81-L93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss

theorem GlobalTheory.HL.DivisibleGauss.index_span_involution {A : Type*} [CommRing A] (c : A →+* A) (hc : ∀ x, c (c x) = x)
    (x : A) :
    (Ideal.span {c x}).toAddSubgroup.index = (Ideal.span {x}).toAddSubgroup.index := by sorry
