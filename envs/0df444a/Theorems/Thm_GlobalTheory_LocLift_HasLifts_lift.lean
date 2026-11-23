-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_HasLifts_lift
-- name    : GlobalTheory.LocLift.HasLifts.lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:16.617833+00:00
-- url     : https://prove2.me/theorems/3d6906cd-9f02-468d-9b71-aefe10ed9c85
-- title:
--   Has Lifts: lift
-- statement:
--   The Has Lifts construction uses the lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L157-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L157-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
omit [GrpObj G]

theorem GlobalTheory.LocLift.HasLifts.lift {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} (h : HasLifts B y e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {W : Set V} {β : V → (Fin m → ℂ)} (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    {w₀ : V} {z₀ : Fin g → ℂ} (hW : IsOpen W) (hw₀ : w₀ ∈ W) (hβ : DifferentiableOn ℂ β W)
    (hm : Set.MapsTo β W B) (hx : IsHolTo W (fun w => (x w).left)) (h0 : e (β w₀) z₀ = x w₀) :
    ∃ ζ : V → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by sorry
