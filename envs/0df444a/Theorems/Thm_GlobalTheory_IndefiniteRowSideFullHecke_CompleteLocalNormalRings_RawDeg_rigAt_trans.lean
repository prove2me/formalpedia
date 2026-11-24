-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_rigAt_trans
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.rigAt_trans
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:13:04.507794+00:00
-- url     : https://prove2.me/theorems/5f96c0a4-5c2e-429e-9451-a3bf96e47a63
-- title:
--   Raw Deg: rig At trans
-- statement:
--   The Raw Deg construction uses the rig At trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L256-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L256-L282

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.rigAt_trans (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.rigAt i V h) =
      D.gAt (pzero D.P.A (genPt R)).left i i' W hW * res k' (D.rigAt i' V' h') := by sorry
