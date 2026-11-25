-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_pull_pull
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.pull_pull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:41.834928+00:00
-- url     : https://prove2.me/theorems/ca30fb25-3c00-556a-9aaa-d2010b204dd2
-- title:
--   Raw Deg: pull pull
-- statement:
--   The Raw Deg construction uses the pull pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L231-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.pull_pull {Y Z Z' : Scheme.{0}} (f : Z ⟶ Y) (g : Z' ⟶ Z) (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    pullU g _ (pullU f U u) = pullU (g ≫ f) U u := by sorry
