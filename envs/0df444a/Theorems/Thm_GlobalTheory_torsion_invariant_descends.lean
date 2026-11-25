-- Prove2me | Theorems.Thm_GlobalTheory_torsion_invariant_descends
-- name    : GlobalTheory.torsion_invariant_descends
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:40.525738+00:00
-- url     : https://prove2.me/theorems/d0f533f5-7cf8-4412-9911-c2553d39fb48
-- title:
--   Global Theory: torsion invariant descends
-- statement:
--   The Global Theory construction uses the torsion invariant descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L167-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L167-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.torsion_invariant_descends :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
        (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ),
      (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)),
      (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 →
        ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤
          ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)),
          (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) →
      ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f := by sorry
