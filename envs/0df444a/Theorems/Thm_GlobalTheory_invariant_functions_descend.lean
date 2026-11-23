-- Prove2me | Theorems.Thm_GlobalTheory_invariant_functions_descend
-- name    : GlobalTheory.invariant_functions_descend
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.718782+00:00
-- url     : https://prove2.me/theorems/10ceaf00-9c5c-426e-be0d-46c0fee938ed
-- title:
--   Global Theory: invariant functions descend
-- statement:
--   The Global Theory construction uses the invariant functions descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L125-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L125-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
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

theorem GlobalTheory.invariant_functions_descend :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (U : B.left.Opens), Function.Injective (q.left.app U).hom ∧ (∀ a : Γ(B.left, U), IsUnit ((q.left.app U).hom a) → IsUnit a) ∧ ∀ f : Γ(G.left, q.left ⁻¹ᵁ U), (∀ (Z : Over S) (t : Z ⟶ T) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ U)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f) → ∃ a : Γ(B.left, U), (q.left.app U).hom a = f := by sorry
