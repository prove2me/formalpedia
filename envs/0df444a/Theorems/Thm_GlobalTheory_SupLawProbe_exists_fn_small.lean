-- Prove2me | Theorems.Thm_GlobalTheory_SupLawProbe_exists_fn_small
-- name    : GlobalTheory.SupLawProbe.exists_fn_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:56.974404+00:00
-- url     : https://prove2.me/theorems/98f6e05d-bbb7-5942-8a7f-bd30dca83b00
-- title:
--   Sup Law Probe: exists fn small
-- statement:
--   The Sup Law Probe construction uses the exists fn small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L157-L163

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
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem GlobalTheory.SupLawProbe.exists_fn_small (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : n ≠ 0) (f : Rul Xo c) :
    ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ,
      FnNe Xo c fn ∧ SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f ≤ 1 := by sorry
