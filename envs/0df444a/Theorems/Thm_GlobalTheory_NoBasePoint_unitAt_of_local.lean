-- Prove2me | Theorems.Thm_GlobalTheory_NoBasePoint_unitAt_of_local
-- name    : GlobalTheory.NoBasePoint.unitAt_of_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:46.065508+00:00
-- url     : https://prove2.me/theorems/a844d63c-183c-47e2-b010-a0f18d77c24c
-- title:
--   No Base Point: unit At of local
-- statement:
--   The No Base Point construction uses the unit At of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSecValueIsUnit.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSecValueIsUnit.lean#L71-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left}

theorem GlobalTheory.NoBasePoint.unitAt_of_local (hL : L.IsLB) {T : Over S} [Subsingleton T.left] {I : Type} [Fintype I]
    (φ : I → ((T ⊗ A).left ⟶ A.left)) (ε : I → ℤ) (p : T.left) (V : T.left.Opens) (hp : p ∈ V)
    (c : LB.Gen ((LB.LinComb L φ ε).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) (y : (T ⊗ A).left) :
    UnitAt L φ ε y := by sorry
