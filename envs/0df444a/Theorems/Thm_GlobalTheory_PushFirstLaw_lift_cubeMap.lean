-- Prove2me | Theorems.Thm_GlobalTheory_PushFirstLaw_lift_cubeMap
-- name    : GlobalTheory.PushFirstLaw.lift_cubeMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:42.641286+00:00
-- url     : https://prove2.me/theorems/8256e381-e758-537f-94ac-f1d0a911906e
-- title:
--   Push First Law: lift cube Map
-- statement:
--   The Push First Law construction uses the lift cube Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L77-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstPartialLawPushAlongTripleMap.lean#L77-L99

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

theorem GlobalTheory.PushFirstLaw.lift_cubeMap {S : Scheme.{0}} {G' G T : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (a : Fin 3 → (T ⟶ G')) (b : Fin 3 → (T ⟶ G)) (h : ∀ i, (b i).left = (a i).left ≫ m.F) :
    (lift (b 0) (lift (b 1) (b 2))).left = (lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3 := by sorry
