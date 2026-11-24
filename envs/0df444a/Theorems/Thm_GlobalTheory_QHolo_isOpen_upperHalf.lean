-- Prove2me | Theorems.Thm_GlobalTheory_QHolo_isOpen_upperHalf
-- name    : GlobalTheory.QHolo.isOpen_upperHalf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:04:08.413227+00:00
-- url     : https://prove2.me/theorems/e24b8219-433a-4abd-a661-11c0fd9e4fa8
-- title:
--   QHolo: is Open upper Half
-- statement:
--   The QHolo construction uses the is Open upper Half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnHilbertEisensteinWeightTwoSeries.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnHilbertEisensteinWeightTwoSeries.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdeaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnHilbertEisensteinWeightTwoSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.QHolo
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.QHolo.isOpen_upperHalf : IsOpen (upperHalf F) := by sorry
