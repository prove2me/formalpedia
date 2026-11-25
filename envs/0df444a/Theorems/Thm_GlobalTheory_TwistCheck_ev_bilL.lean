-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_ev_bilL
-- name    : GlobalTheory.TwistCheck.ev_bilL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:25.202333+00:00
-- url     : https://prove2.me/theorems/ce77cec4-5cce-421f-8429-b3c3802763fe
-- title:
--   Twist Check: ev bil L
-- statement:
--   The Twist Check construction uses the ev bil L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L100-L104

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

theorem GlobalTheory.TwistCheck.ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (bilL G cc) = ∑ i, ∑ l, C (cc i l) * (ev ![a 0] (logOf G i) * ev ![a 1] (logOf G l)) := by sorry
