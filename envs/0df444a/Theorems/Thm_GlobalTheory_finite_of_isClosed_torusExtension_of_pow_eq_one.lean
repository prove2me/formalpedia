-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isClosed_torusExtension_of_pow_eq_one
-- name    : GlobalTheory.finite_of_isClosed_torusExtension_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:05.87092+00:00
-- url     : https://prove2.me/theorems/74bc8ca8-24f6-44ea-8f84-a662dd913043
-- title:
--   Global Theory: finite of is Closed torus Extension of pow eq one
-- statement:
--   The Global Theory construction uses the finite of is Closed torus Extension of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedTorusExtensionOfPowEqOne.lean#L35-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedTorusExtensionOfPowEqOne.lean#L35-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open RationalPoint

theorem GlobalTheory.finite_of_isClosed_torusExtension_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ), LocallyOfFiniteType G.hom → QuasiCompact G.hom → Nonempty (TorusExtension G) → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by sorry
