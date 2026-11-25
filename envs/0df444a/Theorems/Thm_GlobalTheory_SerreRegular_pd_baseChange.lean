-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_pd_baseChange
-- name    : GlobalTheory.SerreRegular.pd_baseChange
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:12.444637+00:00
-- url     : https://prove2.me/theorems/664730fe-d5fa-4c9d-8798-79bea82557f5
-- title:
--   Serre Regular: pd base Change
-- statement:
--   The Serre Regular construction uses the pd base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L13-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular

theorem GlobalTheory.SerreRegular.pd_baseChange {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (Good : ModuleCat.{0} A → Prop)
    (hG : ∀ (M : ModuleCat.{0} A) (r : ℕ) (f : (Fin r → A) →ₗ[A] M), Function.Surjective f →
      Good M → Good (ModuleCat.of A (LinearMap.ker f)) ∧
        Function.Injective ((LinearMap.ker f).subtype.lTensor B)) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], Good M → HasProjectiveDimensionLE M n →
      HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n := by sorry
