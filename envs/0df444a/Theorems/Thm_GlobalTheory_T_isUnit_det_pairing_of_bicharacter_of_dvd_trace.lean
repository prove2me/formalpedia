-- Prove2me | Theorems.Thm_GlobalTheory_T_isUnit_det_pairing_of_bicharacter_of_dvd_trace
-- name    : GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:46.49557+00:00
-- url     : https://prove2.me/theorems/5cd2d54b-9761-435d-9acc-6415dcf2461b
-- title:
--   T: is Unit det pairing of bicharacter of dvd trace
-- statement:
--   The T construction uses the is Unit det pairing of bicharacter of dvd trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsUnitDetPairingOfBicharacterOfDvdTraceStatement.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsUnitDetPairingOfBicharacterOfDvdTraceStatement.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct

theorem GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace : ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by sorry
