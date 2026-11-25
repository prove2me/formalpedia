-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_normVal_vp_p
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.normVal_vp_p
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:40.723311+00:00
-- url     : https://prove2.me/theorems/f7646d23-80e2-444a-88a0-d910a5940f3e
-- title:
--   Generator Values: norm Val vp p
-- statement:
--   The Generator Values construction uses the norm Val vp p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L242-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L242-L246

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
variable [IsLocalRing R] {F : Type} [NormedField F]
variable {φ : FractionRing R →+* F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.normVal_vp_p (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) :
    (normVal_vp hφ hp).toFun (toUnitK (p : R) hp.ne_zero) = 1 := by sorry
