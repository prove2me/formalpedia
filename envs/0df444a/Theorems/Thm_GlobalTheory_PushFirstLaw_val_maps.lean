-- Prove2me | Theorems.Thm_GlobalTheory_PushFirstLaw_val_maps
-- name    : GlobalTheory.PushFirstLaw.val_maps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:08:55.746416+00:00
-- url     : https://prove2.me/theorems/9a0abcd6-ac04-4c03-80dd-c91406161fe7
-- title:
--   Push First Law: val maps
-- statement:
--   The Push First Law construction uses the val maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L26-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushFirstLaw
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)
variable {w z J J'}

theorem GlobalTheory.PushFirstLaw.val_maps (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {b : LB.Gen (LB.LinComb (L.pull F) φ ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ ε) g b) (r : Z ⟶ Y) :
    gm r z (LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F)) (b.s fun k _ => J ((r ≫ φ k) ≫ F)) =
      (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by sorry
