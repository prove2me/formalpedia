-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_periodForm_symm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.periodForm_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:47.406059+00:00
-- url     : https://prove2.me/theorems/cdafe45d-f635-4c53-aa7c-acef5e0f671f
-- title:
--   Generator Values: period Form symm
-- statement:
--   The Generator Values construction uses the period Form symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L113-L114

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.periodForm_symm (D : DegPre R) (a b : D.X) : periodForm v D a b = periodForm v D b a := by sorry
