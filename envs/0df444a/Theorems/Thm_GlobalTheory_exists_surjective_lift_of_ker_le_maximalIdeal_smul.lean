-- Prove2me | Theorems.Thm_GlobalTheory_exists_surjective_lift_of_ker_le_maximalIdeal_smul
-- name    : GlobalTheory.exists_surjective_lift_of_ker_le_maximalIdeal_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:31.717165+00:00
-- url     : https://prove2.me/theorems/5fde7d76-c4ca-468f-a136-d346c7a41910
-- title:
--   Global Theory: exists surjective lift of ker le maximal Ideal smul
-- statement:
--   The Global Theory construction uses the exists surjective lift of ker le maximal Ideal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleGeneratorsTowerLocalRing.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleGeneratorsTowerLocalRing.lean#L32-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleGeneratorsTowerLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_surjective_lift_of_ker_le_maximalIdeal_smul {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {A B : Type} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [AddCommGroup B] [Module Λ B]
    (t : A →ₗ[Λ] B) (ht : Function.Surjective t)
    (hk : LinearMap.ker t ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ A))
    {a : ℕ} (p : (Fin a → Λ) →ₗ[Λ] B) (hp : Function.Surjective p) :
    ∃ q : (Fin a → Λ) →ₗ[Λ] A, Function.Surjective q ∧ t ∘ₗ q = p := by sorry
