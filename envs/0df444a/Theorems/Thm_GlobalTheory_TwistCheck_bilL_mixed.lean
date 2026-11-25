-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_bilL_mixed
-- name    : GlobalTheory.TwistCheck.bilL_mixed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:15.432552+00:00
-- url     : https://prove2.me/theorems/9abc24f3-cb45-419b-a7ac-4162c5caf4ae
-- title:
--   Twist Check: bil L mixed
-- statement:
--   The Twist Check construction uses the bil L mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L145-L152

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

theorem GlobalTheory.TwistCheck.bilL_mixed (G : FGLaw S d) (cc : Fin d → Fin d → S) (i l : Fin d) :
    constantCoeff (pderiv S ((0 : Fin 2), i) (pderiv S ((1 : Fin 2), l) (bilL G cc))) = cc i l := by sorry
