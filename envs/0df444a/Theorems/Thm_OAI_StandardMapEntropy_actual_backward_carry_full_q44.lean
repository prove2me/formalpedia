-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_backward_carry_full_q44
-- name    : OAI.StandardMapEntropy.actual_backward_carry_full_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:13:45.901594+00:00
-- url     : https://prove2.me/theorems/5a746d02-0ec7-4646-9dc4-3c0b908987cb
-- title:
--   OAI.StandardMapEntropy.actual_backward_carry_full_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_backward_carry_full` of [lean/OAI/Dynamics/StandardMap/StandardMap/TransportCarry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TransportCarry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped Topology ENNReal`):
--
--   ```lean
--   lemma actual_backward_carry_full_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
--       (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
--       (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
--       (D : Set ℝ) (X X' : ℝ → ℝ) (l u : ℝ)
--       (hlen : u-l < 1/4)
--       (hXI : ∀ y ∈ D, X y ∈ Icc l u)
--       (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
--       (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
--       (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
--       (htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1)
--       (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
--       (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
--         |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
--           12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
--       ∃ Θ : ℝ × ℝ → ℝ, ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
--         ContinuousOn Θ (Icc l u ×ˢ D) ∧
--         (∀ y ∈ D, Θ (X y,y)=y) ∧
--         (∀ y ∈ D, ∀ v ∈ Icc l u,
--           liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1)) ∧
--         InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (Icc l u ×ˢ D) ∧
--         (∀ z ∈ Icc l u ×ˢ D, HasFDerivWithinAt (fun w => (w.1,Θ w)) (J z) (Icc l u ×ˢ D) z) ∧
--         (∀ z ∈ Icc l u ×ˢ D,
--           Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) ≤ |(J z).det| ∧
--           |(J z).det| ≤ Real.exp (1152*Real.pi)*(1+(24/growthBase k^((4/5:ℝ)))^2)) ∧
--         (∀ y ∈ D, ∀ v ∈ Icc l u,
--           |Θ (v,y)-y| ≤ (24/growthBase k^((4/5:ℝ)))*|v-X y| ∧
--           ∀ i : Fin n, |liftedOrbit k v (Θ (v,y)) (i+1)-liftedOrbit k (X y) y (i+1)| ≤
--             8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.liftedOrbit`, `OAI.StandardMapEntropy.orbitCoefficient` and `OAI.StandardMapEntropy.tSolution` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.dirichletSolution` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.actual_grid_square_product_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TransportCarry.lean (declaration OAI.StandardMapEntropy.actual_backward_carry_full)

import Mathlib
import Definitions.Def_OAIQ44C002

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma actual_backward_carry_full_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (D : Set ℝ) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ Θ : ℝ × ℝ → ℝ, ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ContinuousOn Θ (Icc l u ×ˢ D) ∧
      (∀ y ∈ D, Θ (X y,y)=y) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1)) ∧
      InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (Icc l u ×ˢ D) ∧
      (∀ z ∈ Icc l u ×ˢ D, HasFDerivWithinAt (fun w => (w.1,Θ w)) (J z) (Icc l u ×ˢ D) z) ∧
      (∀ z ∈ Icc l u ×ˢ D,
        Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)*(1+(24/growthBase k^((4/5:ℝ)))^2)) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        |Θ (v,y)-y| ≤ (24/growthBase k^((4/5:ℝ)))*|v-X y| ∧
        ∀ i : Fin n, |liftedOrbit k v (Θ (v,y)) (i+1)-liftedOrbit k (X y) y (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  sorry
end StandardMapEntropy

end OAI
end
