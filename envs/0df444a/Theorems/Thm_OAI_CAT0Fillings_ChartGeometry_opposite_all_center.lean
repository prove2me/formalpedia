-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_opposite_all_center
-- name    : OAI.CAT0Fillings.ChartGeometry.opposite_all_center
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:51:48.033169+00:00
-- url     : https://prove2.me/theorems/939c50c0-41a9-4a73-95e3-37b9e69cb6f5
-- title:
--   OAI.CAT0Fillings.ChartGeometry.opposite_all_center: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.ChartGeometry.opposite_all_center` of [lean/OAI/Geometry/CAT0Fillings/Euler/OppositeIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/OppositeIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.ChartGeometry`, with `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma opposite_all_center (hz : IsCycle T) (o : X) (v : q.Sobolev) {β : ℝ} (hb : 0 < β)
--       (hn : (k+1:ℝ)*β = 1+2*β)
--       (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
--       (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
--       (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
--         (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
--         (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
--           (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
--       (heuler : ∀ ψ : q.Sobolev,
--         4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
--           (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
--         (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
--       (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
--         (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
--       (∫ x, (q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT)^2 ≤
--         (∫ x, (q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT)*
--         (∫ x, dist o x^2*(q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.ChartGeometry.radialVariation` and `OAI.CAT0Fillings.ChartGeometry.sweptMass` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCycle` and `OAI.CAT0Fillings.IsMetricCurrent` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/OppositeIntegral.lean (declaration OAI.CAT0Fillings.ChartGeometry.opposite_all_center)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma opposite_all_center (hz : IsCycle T) (o : X) (v : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    (∫ x, (q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT)^2 ≤
      (∫ x, (q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT)*
      (∫ x, dist o x^2*(q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT) := by
  sorry
end CAT0Fillings.ChartGeometry
end

end OAI
end
