-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_ord_vp_p
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vp_p
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:17.968028+00:00
-- url     : https://prove2.me/theorems/72768b89-a9b7-5191-be49-d0f977b7534b
-- title:
--   Generator Values: ord vp p
-- statement:
--   The Generator Values construction uses the ord vp p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L185-L187

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
variable [IsDiscreteValuationRing R]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vp_p {p : ℕ} (hp : IsOverPrime R p) :
    (ord_vp hp).toFun (toUnitK (p : R) hp.ne_zero) = 1 := by sorry
