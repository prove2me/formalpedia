-- Prove2me | Theorems.Thm_GlobalTheory_FourKTest_secondCountable
-- name    : GlobalTheory.FourKTest.secondCountable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:59.885785+00:00
-- url     : https://prove2.me/theorems/ae7c0cb5-a696-48dc-b832-1b2a0fa771ba
-- title:
--   Four KTest: second Countable
-- statement:
--   The Four KTest construction uses the second Countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppo.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppo.lean#L34-L40

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

theorem GlobalTheory.FourKTest.secondCountable [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by sorry
