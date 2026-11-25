-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticNormality_completion_isDomain_and_isIntegrallyClosed
-- name    : GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:55:06.406721+00:00
-- url     : https://prove2.me/theorems/e4b1cb13-9bfe-5699-b44a-ef6911b169bf
-- title:
--   Analytic Normality: completion is Domain and is Integrally Closed
-- statement:
--   The Analytic Normality construction uses the completion is Domain and is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CompletionIsDomainAndIsIntegrallyClosed.lean#L14-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CompletionIsDomainAndIsIntegrallyClosed.lean#L14-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobsonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsConductorAdicCompletionEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticNormality
open IsLocalRing

theorem GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by sorry
