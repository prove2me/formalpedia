-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_IsDeg_io_isPt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.IsDeg.io_isPt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:48.165337+00:00
-- url     : https://prove2.me/theorems/22274abe-4f56-4e05-958b-083fdc5507e3
-- title:
--   Is Deg: io is Pt
-- statement:
--   The Is Deg construction uses the io is Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L325-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L325-L326

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.IsDeg.io_isPt {D : RawDeg R} {I : Ideal R} (h : D.IsDeg I) (y : D.X) : (D.io y).IsPt := by sorry
