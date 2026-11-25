-- Prove2me | Theorems.Thm_GlobalTheory_HomLinear_exists_linear_of_isMonHom
-- name    : GlobalTheory.HomLinear.exists_linear_of_isMonHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:15.322496+00:00
-- url     : https://prove2.me/theorems/a8b5b672-8511-451f-b681-4d674ec0bee0
-- title:
--   Hom Linear: exists linear of is Mon Hom
-- statement:
--   The Hom Linear construction uses the exists linear of is Mon Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L73-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L73-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem GlobalTheory.HomLinear.exists_linear_of_isMonHom :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
  ∀ (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g'),
  (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) →
  ∀ f : A ⟶ A', IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ z, u'.ex (F z) = u.ex z ≫ f) ∧
    (∀ l ∈ u.Λ, F l ∈ u'.Λ) ∧ (∀ w v, IsTangent v → u.IsDiff w v → IsTangent (v ≫ f) ∧ u'.IsDiff (F w) (v ≫ f)) ∧
    ∀ f' : A ⟶ A', (∀ z, u'.ex (F z) = u.ex z ≫ f') → f' = f := by sorry
