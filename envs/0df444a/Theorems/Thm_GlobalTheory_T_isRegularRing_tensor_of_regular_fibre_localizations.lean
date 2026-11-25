-- Prove2me | Theorems.Thm_GlobalTheory_T_isRegularRing_tensor_of_regular_fibre_localizations
-- name    : GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:37.764802+00:00
-- url     : https://prove2.me/theorems/9a72d9c6-196c-4d2e-b55e-b56cf498e7dd
-- title:
--   T: is Regular Ring tensor of regular fibre localizations
-- statement:
--   The T construction uses the is Regular Ring tensor of regular fibre localizations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularRingTensorOfFibreLocalRingsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularRingTensorOfFibreLocalRingsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRingsStatement
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

theorem GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q → IsRegularLocalRing (Localization.AtPrime n ⧸ (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) → IsRegularRing (T ⊗[S] K) := by sorry
