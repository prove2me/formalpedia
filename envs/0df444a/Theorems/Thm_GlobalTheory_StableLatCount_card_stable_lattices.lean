-- Prove2me | Theorems.Thm_GlobalTheory_StableLatCount_card_stable_lattices
-- name    : GlobalTheory.StableLatCount.card_stable_lattices
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:43.358802+00:00
-- url     : https://prove2.me/theorems/470f24ab-7bf3-43aa-bb0d-2d426d79cd2e
-- title:
--   Stable Lat Count: card stable lattices
-- statement:
--   The Stable Lat Count construction uses the card stable lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableLattices.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableLattices.lean#L16-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardCommMapsEqCardHomQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKernelQuotOfBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.StableLatCount.card_stable_lattices : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by sorry
