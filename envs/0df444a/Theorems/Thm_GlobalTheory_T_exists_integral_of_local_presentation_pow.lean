-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_of_local_presentation_pow
-- name    : GlobalTheory.T.exists_integral_of_local_presentation_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:36.552831+00:00
-- url     : https://prove2.me/theorems/0d5d41b8-b3d4-44f9-b5d6-3355af2fea41
-- title:
--   T: exists integral of local presentation pow
-- statement:
--   The T construction uses the exists integral of local presentation pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIntegralOfLocalPresentationPowStatement.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIntegralOfLocalPresentationPowStatement.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct

theorem GlobalTheory.T.exists_integral_of_local_presentation_pow : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by sorry
