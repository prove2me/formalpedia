-- Prove2me | Theorems.Thm_GlobalTheory_LeviZero_jet_nM
-- name    : GlobalTheory.LeviZero.jet_nM
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:03:31.178557+00:00
-- url     : https://prove2.me/theorems/86719a52-5862-4a94-b41f-ce31d771777a
-- title:
--   Levi Zero: jet n M
-- statement:
--   The Levi Zero construction uses the jet n M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L301-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L301-L310

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
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

theorem GlobalTheory.LeviZero.jet_nM (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) :
    HasJet ξ 0 (fun z => ExF.nM X z τ a b) ((if a = b then 1 else 0) + sJ * cH (zMat X ξ τ a b)) := by sorry
