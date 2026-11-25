-- Prove2me | Theorems.Thm_GlobalTheory_LeviZero_gram_cpt_apply
-- name    : GlobalTheory.LeviZero.gram_cpt_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:11.214207+00:00
-- url     : https://prove2.me/theorems/94c3e7be-ca90-46b1-81a2-4ccc4acf9046
-- title:
--   Levi Zero: gram cpt apply
-- statement:
--   The Levi Zero construction uses the gram cpt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L324-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L324-L332

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.LeviZero.gram_cpt_apply {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) (b c : Fin r) :
    gram τ.1 X.Gm (mat (cpt X x0 z) τ) b c =
      ∑ a, ExF.nM X z τ a b * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (ExF.nM X z τ a c) := by sorry
