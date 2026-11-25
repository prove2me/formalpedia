-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_bilL_injective
-- name    : GlobalTheory.TwistCheck.bilL_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:29.865281+00:00
-- url     : https://prove2.me/theorems/52f5daae-c34d-4158-9001-e30aacb4837b
-- title:
--   Twist Check: bil L injective
-- statement:
--   The Twist Check construction uses the bil L injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L154-L156

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

theorem GlobalTheory.TwistCheck.bilL_injective (G : FGLaw S d) : Function.Injective (bilL G) := by sorry
