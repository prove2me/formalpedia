-- Prove2me | Theorems.Thm_GlobalTheory_SupLawProbe_evR_map
-- name    : GlobalTheory.SupLawProbe.evR_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:24:10.804423+00:00
-- url     : https://prove2.me/theorems/591e1e4a-de0d-4596-916f-3e5dfb705f90
-- title:
--   Sup Law Probe: ev R map
-- statement:
--   The Sup Law Probe construction uses the ev R map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L29-L40

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

theorem GlobalTheory.SupLawProbe.evR_map (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FT y₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) :
    evR Xo c f y₂ = φ (evR Xo c f y₁) := by sorry
