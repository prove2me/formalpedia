-- Prove2me | Theorems.Thm_GlobalTheory_appLE_basicOpen_surjective_of_mul_mem_range
-- name    : GlobalTheory.appLE_basicOpen_surjective_of_mul_mem_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:44.399548+00:00
-- url     : https://prove2.me/theorems/b12bee0b-5d4c-4741-9960-e42f734a528a
-- title:
--   Global Theory: app LE basic Open surjective of mul mem range
-- statement:
--   The Global Theory construction uses the app LE basic Open surjective of mul mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulM.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulM.lean#L9-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory

theorem GlobalTheory.appLE_basicOpen_surjective_of_mul_mem_range {X Z : Scheme.{0}} (φ : X ⟶ Z) {V : Z.Opens}
    (haff : IsAffineOpen (φ ⁻¹ᵁ V)) (r : Γ(Z, V))
    (h : ∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b)
    (A : Z.Opens) (B : X.Opens) (e : B ≤ φ ⁻¹ᵁ A) (hA : A = Z.basicOpen r)
    (hB : B = X.basicOpen ((φ.app V).hom r)) : Function.Surjective (φ.appLE A B e) := by sorry
