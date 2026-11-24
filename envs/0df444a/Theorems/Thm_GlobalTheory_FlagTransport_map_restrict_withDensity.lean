-- Prove2me | Theorems.Thm_GlobalTheory_FlagTransport_map_restrict_withDensity
-- name    : GlobalTheory.FlagTransport.map_restrict_withDensity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:31:04.143374+00:00
-- url     : https://prove2.me/theorems/6619fe0e-200c-441b-85ea-28ec325496d8
-- title:
--   Flag Transport: map restrict with Density
-- statement:
--   The Flag Transport construction uses the map restrict with Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L57-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
open GlobalTheory GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']
variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)

theorem GlobalTheory.FlagTransport.map_restrict_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} (S : α ≃ᵐ β) (hS : MeasurePreserving S μ ν) {Ω : Set α} {Ω' : Set β}
    (hΩ : S ⁻¹' Ω' = Ω) {d : α → ℝ≥0∞} {d' : β → ℝ≥0∞} (hd : ∀ x, d' (S x) = d x) :
    Measure.map S ((μ.restrict Ω).withDensity d) = (ν.restrict Ω').withDensity d' := by sorry
