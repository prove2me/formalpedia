-- Prove2me | Theorems.Thm_GlobalTheory_HL_DivisibleGauss_index_span_mul
-- name    : GlobalTheory.HL.DivisibleGauss.index_span_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:38.51743+00:00
-- url     : https://prove2.me/theorems/2fc4dc27-900e-46e9-8aa3-a94dfc034128
-- title:
--   Divisible Gauss: index span mul
-- statement:
--   The Divisible Gauss construction uses the index span mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLocalCharacterSum.lean#L52-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLocalCharacterSum.lean#L52-L79

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

theorem GlobalTheory.HL.DivisibleGauss.index_span_mul {A : Type*} [CommRing A] (x y : A) (hx : ∀ z, x * z = 0 → z = 0) :
    (Ideal.span {x * y}).toAddSubgroup.index
      = (Ideal.span {y}).toAddSubgroup.index * (Ideal.span {x}).toAddSubgroup.index := by sorry
