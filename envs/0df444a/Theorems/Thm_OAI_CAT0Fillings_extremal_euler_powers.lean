-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_extremal_euler_powers
-- name    : OAI.CAT0Fillings.extremal_euler_powers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:54:27.141753+00:00
-- url     : https://prove2.me/theorems/48fe3ac1-aa41-48c9-b6a3-e3f68c2eb4d5
-- title:
--   OAI.CAT0Fillings.extremal_euler_powers: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.extremal_euler_powers` of [lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory Metric TopologicalSpace`, `open scoped Topology NNReal ENNReal`, `open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev`):
--
--   ```lean
--   theorem extremal_euler_powers {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
--       {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
--       (hm : 0 < mass T) (q : ChartGeometry hT.1)
--       {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
--       (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
--         ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
--           mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
--       (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
--         d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
--       (v : q.Sobolev)
--       (hv : ∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ q.inclusion v x)
--       (heuler : ∀ ψ : q.Sobolev,
--         (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
--           (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
--         (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) :
--       (∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (currentMassMeasure hT.1)) ∧
--       (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
--         (q.inclusion R : X → ℝ) =ᵐ[currentMassMeasure hT.1] (fun x => (q.inclusion v x)^γ) ∧
--         (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
--           (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.atlasParam`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.RadialSobolev.sobolevP` (definitions bundle `OAIQ29C0001` of this split); `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IntegerRectifiable`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.IsMetricCurrent`, `OAI.CAT0Fillings.boundarySucc`, `OAI.CAT0Fillings.fillingCoefficient`, `OAI.CAT0Fillings.fillingPower` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.normalized_extremal_contradiction` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean (declaration OAI.CAT0Fillings.extremal_euler_powers)

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

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_euler_powers {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    (v : q.Sobolev)
    (hv : ∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ q.inclusion v x)
    (heuler : ∀ ψ : q.Sobolev,
      (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) :
    (∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (currentMassMeasure hT.1)) ∧
    (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[currentMassMeasure hT.1] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w)) := by
  sorry

end CAT0Fillings
end

end OAI
end
