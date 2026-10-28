-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_backward_slice_q3
-- name    : OAI.StandardMapEntropy.actual_backward_slice_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:47:06.50912+00:00
-- url     : https://prove2.me/theorems/dacd3414-0f76-474b-936d-d0475d81b7ea
-- title:
--   OAI.StandardMapEntropy.actual_backward_slice_q3: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy_complete`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_backward_slice` of [lean/OAI/Dynamics/StandardMap/StandardMap/BackwardSlice.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BackwardSlice.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology`):
--
--   ```lean
--   lemma actual_backward_slice_q3 (k : ℝ) (n B : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hk : 0 ≤ k)
--       (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
--       (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
--       (ha : 24/growthBase k^((4/5:ℝ)) ≤ 1/2)
--       (D : Set ℝ) (hD : MeasurableSet D) (X X' : ℝ → ℝ) (l u : ℝ)
--       (hlen : u-l < 1/4) (hlu : Icc l u ⊆ Icc (0:ℝ) 1)
--       (hDunit : D ⊆ Icc (0:ℝ) 1)
--       (hXI : ∀ y ∈ D, X y ∈ Icc l u)
--       (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
--       (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
--       (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
--       (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
--       (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
--         |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
--           12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
--       (W : Torus → ℝ) (hW : Continuous W) (hW0 : ∀ z, 0 ≤ W z) (δ : ℝ) (hδ : 0 ≤ δ)
--       (htransport : ∀ z w : ℝ × ℝ,
--         dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
--           8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) →
--         |W (liftProjection z)-W (liftProjection w)| ≤ δ) :
--       (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
--         (∫⁻ y in D, ENNReal.ofReal (W (liftProjection (X y,y)))) ≤
--       16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
--         (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
--           ENNReal.ofReal δ*volume D
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.dirichletSolution`, `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.liftIter`, `OAI.StandardMapEntropy.liftProjection`, `OAI.StandardMapEntropy.orbitCoefficient` and `OAI.StandardMapEntropy.tSolution` (definitions bundle `OAIQ3St000` of this split); `OAI.StandardMapEntropy.Circle`, `OAI.StandardMapEntropy.Torus` and `OAI.StandardMapEntropy.area` (the published bundle `Def_StandardMapLyapunov`).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.actual_fast_bridge_real_q3` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BackwardSlice.lean (declaration OAI.StandardMapEntropy.actual_backward_slice)

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000

section

attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma actual_backward_slice_q3 (k : ℝ) (n B : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ha : 24/growthBase k^((4/5:ℝ)) ≤ 1/2)
    (D : Set ℝ) (hD : MeasurableSet D) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4) (hlu : Icc l u ⊆ Icc (0:ℝ) 1)
    (hDunit : D ⊆ Icc (0:ℝ) 1)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (W : Torus → ℝ) (hW : Continuous W) (hW0 : ∀ z, 0 ≤ W z) (δ : ℝ) (hδ : 0 ≤ δ)
    (htransport : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) →
      |W (liftProjection z)-W (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
      (∫⁻ y in D, ENNReal.ofReal (W (liftProjection (X y,y)))) ≤
    16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
        ENNReal.ofReal δ*volume D := by
  sorry
end StandardMapEntropy

end OAI
end
