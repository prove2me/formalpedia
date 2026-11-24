-- Prove2me | Theorems.Thm_GlobalTheory_isAffine_and_generated_of_wide_product
-- name    : GlobalTheory.isAffine_and_generated_of_wide_product
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:57.760792+00:00
-- url     : https://prove2.me/theorems/44d62511-2a36-464e-9cae-796499209c71
-- title:
--   Global Theory: is Affine and generated of wide product
-- statement:
--   The Global Theory construction uses the is Affine and generated of wide product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineAndGeneratedOfWideProduct.lean#L46-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineAndGeneratedOfWideProduct.lean#L46-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AffineProduct

theorem GlobalTheory.isAffine_and_generated_of_wide_product : ∀ (R : CommRingCat.{0}) (j : ℕ) (Y : Scheme.{0}) (D : Fin j → Scheme.{0}) (s : Y ⟶ Spec R) (d : ∀ i, D i ⟶ Spec R) (pr : ∀ i, Y ⟶ D i) (w : ∀ i, pr i ≫ d i = s), (∀ (Z : Scheme.{0}) (z : Z ⟶ Spec R) (f : ∀ i, Z ⟶ D i), (∀ i, f i ≫ d i = z) → ∃! g : Z ⟶ Y, g ≫ s = z ∧ ∀ i, g ≫ pr i = f i) → (∀ i, IsAffine (D i)) → IsAffine Y ∧ ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) → (∀ i a, (pr i).appTop.hom a ∈ B) → B = ⊤ := by sorry
