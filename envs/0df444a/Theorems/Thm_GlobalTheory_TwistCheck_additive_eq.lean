-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_additive_eq
-- name    : GlobalTheory.TwistCheck.additive_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:44.123236+00:00
-- url     : https://prove2.me/theorems/e439383a-bf1a-46b0-b7ee-5ca289d2d566
-- title:
--   Twist Check: additive eq
-- statement:
--   The Twist Check construction uses the additive eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L17-L62

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

theorem GlobalTheory.TwistCheck.additive_eq (G : FGLaw S d) (g : PS S 1 d)
    (hg : ev (n := 2) ![G.F] g = ev (n := 2) ![pt S d 0] g + ev (n := 2) ![pt S d 1] g) :
    g = ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j := by sorry
