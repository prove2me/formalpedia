-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_chord_scalar_average
-- name    : OAI.CAT0Fillings.ChartGeometry.chord_scalar_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:49:21.726091+00:00
-- url     : https://prove2.me/theorems/3b88f057-c9af-4351-8310-817da21e0a3b
-- title:
--   OAI.CAT0Fillings.ChartGeometry.chord_scalar_average: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.ChartGeometry.chord_scalar_average` of [lean/OAI/Geometry/CAT0Fillings/Chord/Distribution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Chord/Distribution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.ChartGeometry`, with `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`, `open CAT0Fillings.Conformal`):
--
--   ```lean
--   lemma chord_scalar_average (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
--       (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
--       (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
--       (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
--       (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
--         (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
--           (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
--       (heuler : ∀ ψ : q.Sobolev,
--         4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
--           (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
--         (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
--       (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
--         (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
--       (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
--       (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
--         (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
--       (hmin : ∀ P : q.Sobolev,
--         AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
--           (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
--         AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
--           (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) :
--       let μ := MassMeasure.currentMassMeasure hT
--       let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
--       let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
--       (ChordTransform.transform ν (k+1) b a)^(((k+1:ℝ)-2)/(k+1:ℝ)) ≤
--         ChordAverage.average (((k+1:ℝ)-2)/2) (ChordTransform.transform ν (k+1) b) a
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.AnalyticMinimizer.criticalMass`, `OAI.CAT0Fillings.AnalyticMinimizer.criticalNorm`, `OAI.CAT0Fillings.AnalyticMinimizer.energy`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.ChordAverage.average` and `OAI.CAT0Fillings.ChordTransform.transform` (definitions bundle `OAIQ29C0001` of this split); `OAI.CAT0Fillings.ChartGeometry.radialVariation`, `OAI.CAT0Fillings.ChartGeometry.sweptMass` and `OAI.CAT0Fillings.ChordMeasure.probability` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCycle` and `OAI.CAT0Fillings.IsMetricCurrent` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Chord/Distribution.lean (declaration OAI.CAT0Fillings.ChartGeometry.chord_scalar_average)

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
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma chord_scalar_average (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
    (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) :
    let μ := MassMeasure.currentMassMeasure hT
    let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
    let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
    (ChordTransform.transform ν (k+1) b a)^(((k+1:ℝ)-2)/(k+1:ℝ)) ≤
      ChordAverage.average (((k+1:ℝ)-2)/2) (ChordTransform.transform ν (k+1) b) a := by
  sorry
end CAT0Fillings.ChartGeometry
end

end OAI
end
