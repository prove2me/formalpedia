-- Prove2me | Theorems.Thm_GlobalTheory_SupLawProbe_supBdd_of_fn_zero
-- name    : GlobalTheory.SupLawProbe.supBdd_of_fn_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:09.600478+00:00
-- url     : https://prove2.me/theorems/ed54e282-c8b6-5672-97a7-6b6466331c25
-- title:
--   Sup Law Probe: sup Bdd of fn zero
-- statement:
--   The Sup Law Probe construction uses the sup Bdd of fn zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean#L152-L155

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

theorem GlobalTheory.SupLawProbe.supBdd_of_fn_zero (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : n ≠ 0) (f : Rul Xo c) :
    SupBdd Xo c (fun _ _ _ => 0) a n f ∧ ∀ σ, supR Xo c (fun _ _ _ => 0) σ a n f = 0 := by sorry
