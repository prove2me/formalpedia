-- Prove2me | Theorems.Thm_GlobalTheory_PairUnfold_pairDens_rmul
-- name    : GlobalTheory.PairUnfold.pairDens_rmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:43.729671+00:00
-- url     : https://prove2.me/theorems/4967c037-da30-590c-9d14-825da004b783
-- title:
--   Pair Unfold: pair Dens rmul
-- statement:
--   The Pair Unfold construction uses the pair Dens rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PairUnfoldOfUnfold.lean#L37-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PairUnfoldOfUnfold.lean#L37-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PairUnfoldOfUnfold
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
open GlobalTheory GlobalTheory.PairUnfold
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PairUnfold.pairDens_rmul {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) :
    ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, pairDens X P f0 W (rmul x b) = pairDens X P f0 W x := by sorry
