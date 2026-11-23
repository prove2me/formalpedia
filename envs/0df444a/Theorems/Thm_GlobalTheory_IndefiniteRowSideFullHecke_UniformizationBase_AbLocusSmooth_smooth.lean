-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformizationBase_AbLocusSmooth_smooth
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.AbLocusSmooth.smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:51.016111+00:00
-- url     : https://prove2.me/theorems/080bb391-807b-4838-9163-23a9197caeab
-- title:
--   Ab Locus Smooth: smooth
-- statement:
--   The Ab Locus Smooth construction uses the smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAndSmoothness.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAndSmoothness.lean#L43-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.AbLocusSmooth.smooth {Y : Model Xo c β} (h : AbLocusSmooth Y) (U : Y.X.Opens)
    (hU : (U : Set Y.X) = abLocus Y.t.G) : SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s) := by sorry
