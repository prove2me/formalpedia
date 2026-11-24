-- Prove2me | Theorems.Thm_GlobalTheory_sl2Map_nS
-- name    : GlobalTheory.sl2Map_nS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:36.961886+00:00
-- url     : https://prove2.me/theorems/58dfd8b3-6ebb-437b-8910-4aa84049274e
-- title:
--   Global Theory: sl2 Map n S
-- statement:
--   The Global Theory construction uses the sl2 Map n S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWeilRepSL2HermitianBlock.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWeilRepSL2HermitianBlock.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianLinearEquivContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceTowerFiniteEtaleHermitianPairStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceEqSumCoordsOfAlgEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2HermitianBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by sorry
