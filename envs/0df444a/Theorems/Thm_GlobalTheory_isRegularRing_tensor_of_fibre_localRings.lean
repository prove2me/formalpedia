-- Prove2me | Theorems.Thm_GlobalTheory_isRegularRing_tensor_of_fibre_localRings
-- name    : GlobalTheory.isRegularRing_tensor_of_fibre_localRings
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:47.978813+00:00
-- url     : https://prove2.me/theorems/140b8e5d-992a-45ad-8936-e92883d1333b
-- title:
--   Global Theory: is Regular Ring tensor of fibre local Rings
-- statement:
--   The Global Theory construction uses the is Regular Ring tensor of fibre local Rings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularRingTensorOfFibreLocalRings.lean#L6-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularRingTensorOfFibreLocalRings.lean#L6-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isRegularRing_tensor_of_fibre_localRings :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by sorry
