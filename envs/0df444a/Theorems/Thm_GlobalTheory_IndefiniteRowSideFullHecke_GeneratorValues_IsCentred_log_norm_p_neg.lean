-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_IsCentred_log_norm_p_neg
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsCentred.log_norm_p_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:45.421132+00:00
-- url     : https://prove2.me/theorems/29a33353-43ed-4a8e-a309-b2897188619a
-- title:
--   Is Centred: log norm p neg
-- statement:
--   The Is Centred construction uses the log norm p neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L225-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L225-L230

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsCentred.log_norm_p_neg (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) :
    0 < ‖(p : F)‖ ∧ Real.log ‖(p : F)‖ < 0 := by sorry
