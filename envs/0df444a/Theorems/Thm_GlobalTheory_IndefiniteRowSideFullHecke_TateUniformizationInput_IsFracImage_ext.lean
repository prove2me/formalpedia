-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TateUniformizationInput_IsFracImage_ext
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.IsFracImage.ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:26.326086+00:00
-- url     : https://prove2.me/theorems/ddbbba82-4e9a-4598-9f1c-893ef44842a2
-- title:
--   Is Frac Image: ext
-- statement:
--   The Is Frac Image construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TateUniformizationInput.lean#L152-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TateUniformizationInput.lean#L152-L158

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
variable {l : Level H} (c : Coeff l)
variable {c}

theorem GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.IsFracImage.ext {O K : Type} [CommRing O] [Field K] {β : O →+* c.F} (h : IsFracImage β)
    {gam gam' : c.F →+* K} (hgam : ∀ x, gam (β x) = gam' (β x)) : gam = gam' := by sorry
