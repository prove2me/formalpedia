-- Prove2me | Theorems.Thm_GlobalTheory_CompletionReduced_isReduced_adicCompletion
-- name    : GlobalTheory.CompletionReduced.isReduced_adicCompletion
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:52:33.687731+00:00
-- url     : https://prove2.me/theorems/510de8ee-a161-5598-b1a1-2bf8cd44f8a5
-- title:
--   Completion Reduced: is Reduced adic Completion
-- statement:
--   The Completion Reduced construction uses the is Reduced adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionReducedOfJacobson.lean#L122-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionReducedOfJacobson.lean#L122-L134

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionReduced

theorem GlobalTheory.CompletionReduced.isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by sorry
