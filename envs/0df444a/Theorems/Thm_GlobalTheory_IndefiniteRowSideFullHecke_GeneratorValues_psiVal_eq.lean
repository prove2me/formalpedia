-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_psiVal_eq
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.psiVal_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:03.768406+00:00
-- url     : https://prove2.me/theorems/4524cf42-394f-4deb-b86f-be002f9facaa
-- title:
--   Generator Values: psi Val eq
-- statement:
--   The Generator Values construction uses the psi Val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L106-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
variable [IsLocalRing R] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal R Γ)

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.psiVal_eq {D : DegPre R} {χ : D.X} {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    psiVal v D χ = v.toFun x := by sorry
