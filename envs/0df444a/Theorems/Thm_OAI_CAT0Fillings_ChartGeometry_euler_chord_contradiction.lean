-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_euler_chord_contradiction
-- name    : OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:48:33.028771+00:00
-- url     : https://prove2.me/theorems/da2e355e-e4ba-43b6-9864-a3e4e0329343
-- title:
--   OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction` of [lean/OAI/Geometry/CAT0Fillings/Euler/Contradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/Contradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.ChartGeometry`, with `open Set Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open AnalyticMinimizer`):
--
--   ```lean
--   theorem euler_chord_contradiction (hX : IsCAT0 X) (hk : 2 < k+1) (hz : IsCycle T)
--       (v : q.Sobolev) {β : ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
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
--       (hr : ∀ (o : X) (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
--         (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
--       (hW : 0 < criticalMass q.inclusion (2+4*β) v)
--       (hWs : criticalMass q.inclusion (2+4*β) v < sphereArea (k+1))
--       (hE : energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
--         (k+1:ℝ)*criticalMass q.inclusion (2+4*β) v)
--       (hmin : ∀ P : q.Sobolev,
--         energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
--           (criticalNorm q.inclusion (2+4*β) P)^2 ≤
--         energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
--           (criticalNorm q.inclusion (2+4*β) v)^2) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.AnalyticMinimizer.criticalMass`, `OAI.CAT0Fillings.AnalyticMinimizer.criticalNorm`, `OAI.CAT0Fillings.AnalyticMinimizer.energy`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.ChartGeometry.radialVariation` and `OAI.CAT0Fillings.ChartGeometry.sweptMass` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsCycle`, `OAI.CAT0Fillings.IsMetricCurrent` and `OAI.CAT0Fillings.sphereArea` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.normalized_extremal_contradiction` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/Contradiction.lean (declaration OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction)

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
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
theorem euler_chord_contradiction (hX : IsCAT0 X) (hk : 2 < k+1) (hz : IsCycle T)
    (v : q.Sobolev) {β : ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
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
    (hr : ∀ (o : X) (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < criticalMass q.inclusion (2+4*β) v)
    (hWs : criticalMass q.inclusion (2+4*β) v < sphereArea (k+1))
    (hE : energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (criticalNorm q.inclusion (2+4*β) P)^2 ≤
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (criticalNorm q.inclusion (2+4*β) v)^2) : False := by
  sorry
end CAT0Fillings.ChartGeometry
end

end OAI
end
