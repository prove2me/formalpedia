-- Prove2me | Theorems.Thm_GlobalTheory_ClassWeight_classSub_structure
-- name    : GlobalTheory.ClassWeight.classSub_structure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:03.332356+00:00
-- url     : https://prove2.me/theorems/f676c845-eee2-41be-88ec-19c6be532b34
-- title:
--   Class Weight: class Sub structure
-- statement:
--   The Class Weight construction uses the class Sub structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L85-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L85-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]

theorem GlobalTheory.ClassWeight.classSub_structure [Module.Finite ℤ X] [IsAlgClosed F] [FiniteDimensional F E] (hN : (N : F) ≠ 0)
    {A : Type} [CommGroup A] [Finite A] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)) (hA : (Nat.card A : F) ≠ 0)
    (hd : Module.finrank F E ^ 2 = Nat.card A) (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hn : ∀ a, (∀ b, e a b = 1) → a = 1)
    (S : ∀ α, E →ₗ[F] W α) (hS : ∀ v, (∀ α, S α v = 0) → v = 0)
    (a : TorChar X F N →* A) (ha : Function.Injective a)
    (hT : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v)
    (H : Subgroup A) (hH : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v'))
    (hcard : Nat.card (TorChar X F N) * Nat.card H = Nat.card A) (α : X) :
    (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
    Module.finrank F (classSub S N α) * Nat.card (TorChar X F N) = Module.finrank F E ∧
    ∀ U : Submodule F E, U ≤ classSub S N α → (∀ h ∈ H, ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = classSub S N α := by sorry
