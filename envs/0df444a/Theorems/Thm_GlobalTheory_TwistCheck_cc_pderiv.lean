-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_cc_pderiv
-- name    : GlobalTheory.TwistCheck.cc_pderiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:37.041525+00:00
-- url     : https://prove2.me/theorems/1b1ae2c9-0414-4755-8f66-dc5dd2033daf
-- title:
--   Twist Check: cc pderiv
-- statement:
--   The Twist Check construction uses the cc pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L64-L66

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

theorem GlobalTheory.TwistCheck.cc_pderiv (f : PS S 1 d) (j : Fin d) :
    constantCoeff (pderiv S ((0 : Fin 1), j) f) = coeff (Finsupp.single ((0 : Fin 1), j) 1) f := by sorry
