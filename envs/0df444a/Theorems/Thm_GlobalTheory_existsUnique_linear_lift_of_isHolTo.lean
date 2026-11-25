-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_isHolTo
-- name    : GlobalTheory.existsUnique_linear_lift_of_isHolTo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:26.688036+00:00
-- url     : https://prove2.me/theorems/24d9e095-652d-40d4-8400-5e9c94a326fd
-- title:
--   Global Theory: exists Unique linear lift of is Hol To
-- statement:
--   The Global Theory construction uses the exists Unique linear lift of is Hol To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L133-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L133-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set Metric
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TangentOrigin

theorem GlobalTheory.existsUnique_linear_lift_of_isHolTo :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ)
      (u : HolUnif A L g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
      (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
      ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
      IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
      ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by sorry
