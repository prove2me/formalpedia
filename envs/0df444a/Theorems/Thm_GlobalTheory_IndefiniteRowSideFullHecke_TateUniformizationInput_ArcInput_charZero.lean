-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TateUniformizationInput_ArcInput_charZero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput.charZero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:30.752807+00:00
-- url     : https://prove2.me/theorems/f00ee92f-4b8f-57d1-ac1f-3a288ff89634
-- title:
--   Arc Input: char Zero
-- statement:
--   The Arc Input construction uses the char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TateUniformizationInput.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TateUniformizationInput.lean#L211-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
attribute [instance] ArcInput.mod
open GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput.charZero (x : ArcInput D c β O' b) : CharZero (FractionRing O') := by sorry
