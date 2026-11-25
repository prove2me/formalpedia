-- Prove2me | Theorems.Thm_GlobalTheory_PushFirstLaw_val_theta
-- name    : GlobalTheory.PushFirstLaw.val_theta
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:21.759586+00:00
-- url     : https://prove2.me/theorems/ef0c05df-bfe0-5e2e-b0a3-3d086130f3fa
-- title:
--   Push First Law: val theta
-- statement:
--   The Push First Law construction uses the val theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L58-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L58-L73

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
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.PushFirstLaw.val_theta (m : CubeMap G' G) {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L' (L.pull m.F)}
    {c : LB.Gen (Theta G L)} {c' : LB.Gen (Theta G' L')}
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c' (m.thetaPull L c))
    {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} {J' : (Z ⟶ G'.left) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J')
    (r : Z ⟶ (G3 G').left) :
    val (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J =
      (∏ k, isoVal w z J J' (r ≫ thφ G' (x3 G') k) ^ thε k) * val (φ := thφ G' (x3 G')) (ε := thε) c' r z J' := by sorry
