-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussProd_continuous_trace_NL
-- name    : GlobalTheory.JR.WeilQuad.GaussProd.continuous_trace_NL
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:12.9138+00:00
-- url     : https://prove2.me/theorems/37b7a70f-d8fd-466c-b476-f4318bcccde6
-- title:
--   Gauss Prod: continuous trace NL
-- statement:
--   The Gauss Prod construction uses the continuous trace NL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaussIntegralOneMulGaussIntegralNegOneEqOne.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaussIntegralOneMulGaussIntegralNegOneEqOne.lean#L38-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.GaussProd
open GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.GaussProd.continuous_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    Continuous fun y : A.L => Algebra.trace F A.K (x * A.NL y) := by sorry
