-- Prove2me | Theorems.Thm_GlobalTheory_JR_HypJ_main
-- name    : GlobalTheory.JR.HypJ.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:56.736133+00:00
-- url     : https://prove2.me/theorems/3b068b90-0724-407f-b0a9-4b71a39dc8e7
-- title:
--   Hyp J: main
-- statement:
--   The Hyp J construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypMemInducedFourierWeyl.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypMemInducedFourierWeyl.lean#L12-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TestFunctionLocallyInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivarianceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeyl
import Theorems.Thm_GlobalTheory_EtaChar_main
import Theorems.Thm_GlobalTheory_JR_EtFacts_main
import Theorems.Thm_GlobalTheory_JR_TildeTest_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HypJ

theorem GlobalTheory.JR.HypJ.main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by sorry
