-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_log_act
-- name    : GlobalTheory.TwistCheck.log_act
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:53.281773+00:00
-- url     : https://prove2.me/theorems/f9fdd43e-45db-4d4b-99c3-68b9c50d9c96
-- title:
--   Twist Check: log act
-- statement:
--   The Twist Check construction uses the log act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L68-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L68-L98

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BilLActRight
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

theorem GlobalTheory.TwistCheck.log_act {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (i : Fin d) :
    ev (n := 1) ![A.act a] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * logOf G j := by sorry
