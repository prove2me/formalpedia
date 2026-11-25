-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_bilL_act_left
-- name    : GlobalTheory.TwistCheck.bilL_act_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:38.046162+00:00
-- url     : https://prove2.me/theorems/01d03e14-f0d7-4c8e-94ec-ba843f5171fc
-- title:
--   Twist Check: bil L act left
-- statement:
--   The Twist Check construction uses the bil L act left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L117-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L117-L130

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

theorem GlobalTheory.TwistCheck.bilL_act_left {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
      bilL G ((dLin (A.act a)).transpose * Matrix.of cc) := by sorry
