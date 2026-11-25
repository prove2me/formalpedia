-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_log_act_at
-- name    : GlobalTheory.TwistCheck.log_act_at
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:29.18581+00:00
-- url     : https://prove2.me/theorems/a40fd4c6-a92e-40d1-a6d9-e11315d73a50
-- title:
--   Twist Check: log act at
-- statement:
--   The Twist Check construction uses the log act at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L106-L115

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

theorem GlobalTheory.TwistCheck.log_act_at {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (l : Fin 2) (i : Fin d) :
    ev (n := 2) ![comp1 (A.act a) (pt S d l)] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * lg G l j := by sorry
