-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_compact_graph_labels_full_q44
-- name    : OAI.StandardMapEntropy.actual_compact_graph_labels_full_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:14:17.655258+00:00
-- url     : https://prove2.me/theorems/e935f9c1-4699-453f-a7b9-cca9564855ff
-- title:
--   OAI.StandardMapEntropy.actual_compact_graph_labels_full_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_compact_graph_labels_full` of [lean/OAI/Dynamics/StandardMap/StandardMap/TransportGraphs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TransportGraphs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter Metric`, `open scoped Topology`):
--
--   ```lean
--   lemma actual_compact_graph_labels_full_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
--       (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
--       (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
--       (S : Set (ℝ × ℝ)) (hs : IsCompact S)
--       (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
--       (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
--         |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
--           12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
--       (l u yc : ℝ) (hyc : yc ∈ Icc l u) (hlen : u-l < 1/4)
--       (hSp : ∀ z ∈ S, z.1 ∈ Icc l u) :
--       ∃ E : Set ℝ, ∃ X : ℝ × ℝ → ℝ,
--         IsCompact E ∧ ContinuousOn X (E ×ˢ Icc l u) ∧
--         (∀ s ∈ E, X (s,yc)=s) ∧
--         (∀ z ∈ S, ∃ s ∈ E, X (s,z.1)=z.2) ∧
--         InjOn (fun w => (X w,w.2)) (E ×ˢ Icc l u) ∧
--         (∀ s ∈ E, ∀ y ∈ Icc l u,
--           liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1) ∧
--           tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0 ∧
--           HasStrictDerivAt (fun v => X (s,v)) (boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)) y ∧
--           |boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)| ≤ 24/growthBase k^((4/5:ℝ)) ∧
--           Real.exp (-1152*Real.pi) ≤
--             |tSolution (orbitCoefficient k yc s) (n+1)|/
--             |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
--           |tSolution (orbitCoefficient k yc s) (n+1)|/
--             |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) ∧
--         (∀ s ∈ E, ∃ z ∈ S, ∀ y ∈ Icc l u,
--           liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k z.1 z.2 (n+1) ∧
--           |X (s,y)-z.2| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z.1| ∧
--           ∀ i : Fin n, |liftedOrbit k y (X (s,y)) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
--             8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.liftedOrbit`, `OAI.StandardMapEntropy.orbitCoefficient` and `OAI.StandardMapEntropy.tSolution` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.boundaryValue` and `OAI.StandardMapEntropy.dirichletSolution` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI_StandardMapEntropy_actual_fast_bridge_real_q44` and `OAI.StandardMapEntropy.actual_grid_square_product_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TransportGraphs.lean (declaration OAI.StandardMapEntropy.actual_compact_graph_labels_full)

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

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma actual_compact_graph_labels_full_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (S : Set (ℝ × ℝ)) (hs : IsCompact S)
    (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (l u yc : ℝ) (hyc : yc ∈ Icc l u) (hlen : u-l < 1/4)
    (hSp : ∀ z ∈ S, z.1 ∈ Icc l u) :
    ∃ E : Set ℝ, ∃ X : ℝ × ℝ → ℝ,
      IsCompact E ∧ ContinuousOn X (E ×ˢ Icc l u) ∧
      (∀ s ∈ E, X (s,yc)=s) ∧
      (∀ z ∈ S, ∃ s ∈ E, X (s,z.1)=z.2) ∧
      InjOn (fun w => (X w,w.2)) (E ×ˢ Icc l u) ∧
      (∀ s ∈ E, ∀ y ∈ Icc l u,
        liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1) ∧
        tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0 ∧
        HasStrictDerivAt (fun v => X (s,v)) (boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)) y ∧
        |boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)| ≤ 24/growthBase k^((4/5:ℝ)) ∧
        Real.exp (-1152*Real.pi) ≤
          |tSolution (orbitCoefficient k yc s) (n+1)|/
          |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
        |tSolution (orbitCoefficient k yc s) (n+1)|/
          |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) ∧
      (∀ s ∈ E, ∃ z ∈ S, ∀ y ∈ Icc l u,
        liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k z.1 z.2 (n+1) ∧
        |X (s,y)-z.2| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z.1| ∧
        ∀ i : Fin n, |liftedOrbit k y (X (s,y)) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  sorry
end StandardMapEntropy

end OAI
end
