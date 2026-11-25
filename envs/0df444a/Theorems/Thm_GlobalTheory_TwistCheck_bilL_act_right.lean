-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_bilL_act_right
-- name    : GlobalTheory.TwistCheck.bilL_act_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:44.437412+00:00
-- url     : https://prove2.me/theorems/78271ee7-1d89-43dc-b546-90611fef238c
-- title:
--   Twist Check: bil L act right
-- statement:
--   The Twist Check construction uses the bil L act right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L132-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L132-L143

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BilLActRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open GlobalTheory GlobalTheory.TwistCheck
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem GlobalTheory.TwistCheck.bilL_act_right {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (b : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) =
      bilL G (Matrix.of cc * dLin (A.act b)) := by sorry
