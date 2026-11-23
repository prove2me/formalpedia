-- Prove2me | Theorems.Thm_GlobalTheory_FourKTest_betaK_apply
-- name    : GlobalTheory.FourKTest.betaK_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:24.83396+00:00
-- url     : https://prove2.me/theorems/092a9800-db94-488c-891a-31d7dce42316
-- title:
--   Four KTest: beta K apply
-- statement:
--   The Four KTest construction uses the beta K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppo.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppo.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.FourKTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.FourKTest.betaK_apply (A : Et F E) (x y : A.K × A.K) :
    betaK A x y = Algebra.trace F A.K (x.1 * y.2) + Algebra.trace F A.K (x.2 * y.1) := by sorry
