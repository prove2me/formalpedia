-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_ringEquiv_adicCompletion_localization_prod
-- name    : GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:43.2338+00:00
-- url     : https://prove2.me/theorems/27666dd6-10ef-4b63-a9d3-6f5dff9b98cd
-- title:
--   T: exists ring Equiv adic Completion localization prod
-- statement:
--   The T construction uses the exists ring Equiv adic Completion localization prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRingEquivAdicCompletionLocalizationProdStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRingEquivAdicCompletionLocalizationProdStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by sorry
