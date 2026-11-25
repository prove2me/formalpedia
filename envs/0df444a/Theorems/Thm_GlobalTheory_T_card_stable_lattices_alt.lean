-- Prove2me | Theorems.Thm_GlobalTheory_T_card_stable_lattices_alt
-- name    : GlobalTheory.T.card_stable_lattices_alt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:42:13.256947+00:00
-- url     : https://prove2.me/theorems/fd887fd0-80fc-4587-93ca-b3f8839dbdf5
-- title:
--   T: card stable lattices alt
-- statement:
--   The T construction uses the card stable lattices alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableLatticesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableLatticesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_stable_lattices_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by sorry
