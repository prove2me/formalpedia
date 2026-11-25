-- Prove2me | Theorems.Thm_GlobalTheory_T_partialFourier_etaleKProd_locallyConstantCompactSupport
-- name    : GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:00.675778+00:00
-- url     : https://prove2.me/theorems/b7074f29-9e0d-4fe1-8f05-77bc22e97479
-- title:
--   T: partial Fourier etale KProd locally Constant Compact Support
-- statement:
--   The T construction uses the partial Fourier etale KProd locally Constant Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierEtaleKProdLocallyConstantCompactSuStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierEtaleKProdLocallyConstantCompactSuStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSu
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSuStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by sorry
