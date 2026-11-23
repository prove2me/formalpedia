-- Prove2me | Theorems.Thm_GlobalTheory_T_partialFourier_psiK_preserves_testFunctions
-- name    : GlobalTheory.T.partialFourier_psiK_preserves_testFunctions
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:56.628805+00:00
-- url     : https://prove2.me/theorems/696c3710-1fba-4fdb-bc2e-70f20b1f2827
-- title:
--   T: partial Fourier psi K preserves test Functions
-- statement:
--   The T construction uses the partial Fourier psi K preserves test Functions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctionsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctionsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctionsStatement
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

theorem GlobalTheory.T.partialFourier_psiK_preserves_testFunctions : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by sorry
