-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_val_res_eq
-- name    : GlobalTheory.UnitLemma.CayleyCase.val_res_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:58.642245+00:00
-- url     : https://prove2.me/theorems/160e4d47-6fe7-49eb-a427-2b7ab8c875a5
-- title:
--   Cayley Case: val res eq
-- statement:
--   The Cayley Case construction uses the val res eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L122-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L122-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase

theorem GlobalTheory.UnitLemma.CayleyCase.val_res_eq {O E A₁ A₂ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ Y₁ : A₁) (g₂ Y₂ : A₂)
    (hr : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0)
    (hr' : resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly ≠ 0)
    (h₁ : ∀ L : Submodule O A₁, (∀ y ∈ L, g₁ * y ∈ L) ↔ (∀ y ∈ L, Y₁ * y ∈ L))
    (h₂ : ∀ L : Submodule O A₂, (∀ y ∈ L, g₂ * y ∈ L) ↔ (∀ y ∈ L, Y₂ * y ∈ L))
    (h : ∀ L : Submodule O (A₁ × A₂), (∀ y ∈ L, (g₁, g₂) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L))
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) (l₁ : IsLat O E M₁) (l₂ : IsLat O E M₂)
    (s₁ : ∀ y ∈ M₁, g₁ * y ∈ M₁) (s₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) =
      val O (resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly) := by sorry
