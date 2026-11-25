-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_prod_ne_zero
-- name    : GlobalTheory.ThetaTranslJet.exists_prod_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:44.434111+00:00
-- url     : https://prove2.me/theorems/8f6a8f07-c803-4f2c-8942-5f24d556b9c2
-- title:
--   Theta Transl Jet: exists prod ne zero
-- statement:
--   The Theta Transl Jet construction uses the exists prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L70-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L70-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet

theorem GlobalTheory.ThetaTranslJet.exists_prod_ne_zero {σ κ W : Type} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) (f : κ → W → ℂ) (hf : ∀ k, AnalyticAt ℂ (f k) 0) (hf0 : ∀ k, f k 0 = 0)
    (hsp : ∀ c : σ → ℂ, c ≠ 0 → ∃ k, ∑ i, c i * fderiv ℂ (f k) 0 (u i) ≠ 0)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ s : Fin P.totalDegree → κ, ∀ h : W → ℂ, AnalyticAt ℂ h 0 → h 0 ≠ 0 →
      polyDeriv P u (fun z => (∏ j, f (s j) z) * h z) 0 ≠ 0 := by sorry
