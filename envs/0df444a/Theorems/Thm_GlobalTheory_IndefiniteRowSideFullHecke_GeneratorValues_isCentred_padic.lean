-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_isCentred_padic
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.isCentred_padic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:54.955077+00:00
-- url     : https://prove2.me/theorems/fd7f22c1-260a-4f54-a906-751eae5afebb
-- title:
--   Generator Values: is Centred padic
-- statement:
--   The Generator Values construction uses the is Centred padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L262-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L262-L269

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.isCentred_padic (p : ℕ) [Fact p.Prime] :
    IsCentred (R := ℤ_[p]) (FractionRing.algEquiv ℤ_[p] ℚ_[p]).toRingEquiv.toRingHom := by sorry
