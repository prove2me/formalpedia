-- Prove2me | Theorems.Thm_GlobalTheory_TwistCheck_balanced_iff
-- name    : GlobalTheory.TwistCheck.balanced_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:08.015038+00:00
-- url     : https://prove2.me/theorems/001f735e-2c8f-4f6d-8f82-66120163c01c
-- title:
--   Twist Check: balanced iff
-- statement:
--   The Twist Check construction uses the balanced iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/BilLActRight.lean#L158-L163

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

theorem GlobalTheory.TwistCheck.balanced_iff {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a b : O) (cc : Fin d → Fin d → S) :
    (dLin (A.act a)).transpose * Matrix.of cc = Matrix.of cc * dLin (A.act b) ↔
      ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
        ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) := by sorry
