-- Prove2me | Theorems.Thm_GlobalTheory_SupLawProbe_evR_of_not_ft
-- name    : GlobalTheory.SupLawProbe.evR_of_not_ft
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:29:14.953012+00:00
-- url     : https://prove2.me/theorems/5b17a69b-0acc-411c-aa18-338a06589a0a
-- title:
--   Sup Law Probe: ev R of not ft
-- statement:
--   The Sup Law Probe construction uses the ev R of not ft property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupLawProbe
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.SupLawProbe.evR_of_not_ft {S : Type} [CommRing S] [Algebra c.F S] (f : Rul Xo c) (y : FrPt Xo c S) (hy : ¬ FT y) :
    evR Xo c f y = 0 := by sorry
