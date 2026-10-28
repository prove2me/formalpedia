-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_jointly_continuous_dirichlet_family_q44
-- name    : OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:15:01.712593+00:00
-- url     : https://prove2.me/theorems/8e6aad2d-aa79-4036-bdfa-2e3e1dc98940
-- title:
--   OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.jointly_continuous_dirichlet_family` of [lean/OAI/Dynamics/StandardMap/StandardMap/JointGraphFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/JointGraphFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter Metric`, `open scoped Topology`):
--
--   ```lean
--   lemma jointly_continuous_dirichlet_family_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
--       (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
--       (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
--       (s : Set (ℝ × ℝ))
--       (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
--       (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
--         |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
--           12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
--       ∃ b : (ℝ × ℝ) → ℝ → ℝ,
--         ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (s ×ˢ Icc (-(1/4)) (1/4)) ∧
--         ∀ z ∈ s, b z 0=z.2 ∧
--         (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
--         (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
--           |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
--             8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
--         (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
--           |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
--             24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.liftedOrbit`, `OAI.StandardMapEntropy.orbitCoefficient` and `OAI.StandardMapEntropy.tSolution` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.dirichletSolution` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.actual_backward_carry_full_q44` and `OAI.StandardMapEntropy.actual_compact_graph_labels_full_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/JointGraphFamily.lean (declaration OAI.StandardMapEntropy.jointly_continuous_dirichlet_family)

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

lemma jointly_continuous_dirichlet_family_q44 (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (s : Set (ℝ × ℝ))
    (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (s ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ s, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
          24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  sorry
end StandardMapEntropy

end OAI
end
