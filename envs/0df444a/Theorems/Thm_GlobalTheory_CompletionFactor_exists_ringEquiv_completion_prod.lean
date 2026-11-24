-- Prove2me | Theorems.Thm_GlobalTheory_CompletionFactor_exists_ringEquiv_completion_prod
-- name    : GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:22.005174+00:00
-- url     : https://prove2.me/theorems/89b638d2-a0c1-4f89-877a-2bebfbc86aef
-- title:
--   Completion Factor: exists ring Equiv completion prod
-- statement:
--   The Completion Factor construction uses the exists ring Equiv completion prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRingEquivAdicCompletionLocalizationProd.lean#L122-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRingEquivAdicCompletionLocalizationProd.lean#L122-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.CompletionFactor

theorem GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by sorry
