-- Prove2me | Theorems.Thm_GlobalTheory_FourKFub_fourK_eq_fourB_tilde
-- name    : GlobalTheory.FourKFub.fourK_eq_fourB_tilde
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:10.806799+00:00
-- url     : https://prove2.me/theorems/c2b1e6ed-3a1c-4741-97cc-0f3864680402
-- title:
--   Four KFub: four K eq four B tilde
-- statement:
--   The Four KFub construction uses the four K eq four B tilde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierEtaleKEqIntegralPartialFourier.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierEtaleKEqIntegralPartialFourier.lean#L33-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier
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
open GlobalTheory GlobalTheory.FourKFub
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.FourKFub.fourK_eq_fourB_tilde : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by sorry
