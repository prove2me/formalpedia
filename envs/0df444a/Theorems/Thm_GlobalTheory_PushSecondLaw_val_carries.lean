-- Prove2me | Theorems.Thm_GlobalTheory_PushSecondLaw_val_carries
-- name    : GlobalTheory.PushSecondLaw.val_carries
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:07.87261+00:00
-- url     : https://prove2.me/theorems/9b1a5497-fb1d-404b-bdf6-184f1e8302e2
-- title:
--   Push Second Law: val carries
-- statement:
--   The Push Second Law construction uses the val carries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondPartialLawPushAlongTripleMap.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondPartialLawPushAlongTripleMap.lean#L35-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
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
open GlobalTheory GlobalTheory.PushSecondLaw
open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}

theorem GlobalTheory.PushSecondLaw.val_carries {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by sorry
