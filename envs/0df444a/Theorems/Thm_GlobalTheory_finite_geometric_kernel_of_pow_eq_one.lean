-- Prove2me | Theorems.Thm_GlobalTheory_finite_geometric_kernel_of_pow_eq_one
-- name    : GlobalTheory.finite_geometric_kernel_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:11.988801+00:00
-- url     : https://prove2.me/theorems/a755d5ea-b002-4868-9a42-efea59d301b9
-- title:
--   Global Theory: finite geometric kernel of pow eq one
-- statement:
--   The Global Theory construction uses the finite geometric kernel of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfIsReducedOfRangeSubset.lean#L28-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfIsReducedOfRangeSubset.lean#L28-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfIsReducedOfRangeSubset
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

theorem GlobalTheory.finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by sorry
