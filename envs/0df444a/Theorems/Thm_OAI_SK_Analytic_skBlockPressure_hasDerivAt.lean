-- Prove2me | Theorems.Thm_OAI_SK_Analytic_skBlockPressure_hasDerivAt
-- name    : OAI.SK.Analytic.skBlockPressure_hasDerivAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:01:15.639669+00:00
-- url     : https://prove2.me/theorems/28919343-7f25-467f-ae13-641099c4178b
-- title:
--   OAI.SK.Analytic.skBlockPressure_hasDerivAt: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.skBlockPressure_hasDerivAt` of [lean/OAI/Probability/SKBarriers/SKBarriers/Interpolation/SKPressureCurve.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Interpolation/SKPressureCurve.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory Filter`):
--
--   ```lean
--   theorem skBlockPressure_hasDerivAt {N k : ℕ} (hN : 0 < N)
--       (h : ℝ → ℝ) (v : ℝ → Fin (k+1) → ℝ) {t h' : ℝ} {v' : Fin (k+1) → ℝ}
--       (hh : HasDerivAt h h' t) (hv : HasDerivAt v v' t) :
--       let D := Fintype.card (Edge N)
--       let n := blockDimension D N k
--       let U := blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
--       HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
--         ((h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
--           hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l))+
--         ∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
--           hierarchyMeanOverlap n (blockMass D N k) U (fun i s => spin (s i)) (blockLevel D N k l) else 0)) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.ParameterSpace`, `OAI.SK.Analytic.parameterNormedGroup` and `OAI.SK.Analytic.parameterNormedSpace` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.blockDimension`, `OAI.SK.Analytic.blockLevel` and `OAI.SK.Analytic.blockMass` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.blockExponent` and `OAI.SK.Analytic.hierarchyMeanOverlap` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.skInteraction` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.hierarchyReplicaSecond` and `OAI.SK.Analytic.skBlockRoot` (definitions bundle `OAIQ036S004` of this split); `OAI.SK.Config`, `OAI.SK.Edge` and `OAI.SK.spin` (the published bundle `Def_SKBarriers`).
--
--   **Used by.** The proofs of `OAI.SK.Analytic.coverage_energy_tail`, `OAI.SK.Analytic.exists_stationary_quantile_sequence`, `OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf`, `OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf` and `OAI.SK.Analytic.scalarCDFPotential_minimum_bound` of this split import it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Interpolation/SKPressureCurve.lean (declaration OAI.SK.Analytic.skBlockPressure_hasDerivAt)

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockPressure_hasDerivAt {N k : ℕ} (hN : 0 < N)
    (h : ℝ → ℝ) (v : ℝ → Fin (k+1) → ℝ) {t h' : ℝ} {v' : Fin (k+1) → ℝ}
    (hh : HasDerivAt h h' t) (hv : HasDerivAt v v' t) :
    let D := Fintype.card (Edge N)
    let n := blockDimension D N k
    let U := blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
    HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
      ((h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
        hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l))+
      ∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
        hierarchyMeanOverlap n (blockMass D N k) U (fun i s => spin (s i)) (blockLevel D N k l) else 0)) t := by
  sorry
end SK.Analytic

end
end

end

end OAI
end
