-- Prove2me | Theorems.Thm_OAI_Blocks_block_estimates
-- name    : OAI.Blocks.block_estimates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:41:53.026468+00:00
-- url     : https://prove2.me/theorems/21e73ad2-61c1-4d19-9966-88420f3dbf00
-- title:
--   OAI.Blocks.block_estimates: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Blocks.block_estimates` of [lean/OAI/Geometry/TranslativeCovering/Blocks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/Blocks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Blocks`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Finset MeasureTheory BlockGeometry BlockSets`, `open scoped BigOperators`):
--
--   ```lean
--   theorem block_estimates {L C0 c0 : ℝ} (hL : 1 ≤ L) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) :
--       ∃ B K C : ℝ, 0 < B ∧ 0 < K ∧ 0 < C ∧
--       ∀ (Ω : Type u₁) (I : Type u₂) [MeasurableSpace Ω] [StandardBorelSpace Ω]
--         [Fintype I] [Nonempty I] [DecidableEq I] (μ : Measure Ω)
--         [IsFiniteMeasure μ] [NullSingletonClass μ],
--       ∀ (u : ℝ), 1 ≤ u → (Fintype.card I:ℝ) ≤ Real.exp (2*u) →
--       ∀ (caps : I → Set Ω), (∀ i, MeasurableSet (caps i)) → (∀ i, 0 < μ.real (caps i)) →
--       ∀ (d : I → I → ℝ), (∀ i j, 0 ≤ d i j) → (∀ i, d i i = 0) →
--         (∀ i j, d i j = d j i) → (∀ i j k, d i k ≤ d i j+d j k) →
--       (∀ i j, μ.real (caps i ∩ caps j)/Real.sqrt (clipped μ caps i*clipped μ caps j) ≤
--         C0*Real.exp (-c0*d i j^2)) →
--       (∀ S : Finset I, S.Nonempty → radius d S ≤ B*u →
--         ∀ a ∈ S, (∀ i ∈ S, μ.real (caps a) ≤ μ.real (caps i)) →
--         Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ caps a ≤ μ.real (common caps S)) →
--       ∃ (P : Finpartition (univ : Finset I)) (a : Finset I → I) (E : Finset I → Set Ω),
--         (∀ S ∈ P.parts, a S ∈ S ∧ (∀ i ∈ S, μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
--           MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
--           Real.exp (-K*u)*clipped μ caps (a S) ≤ μ.real (E S) ∧
--           0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
--         (∑ S ∈ P.parts, -Real.log (μ.real (E S))) ≤ ∑ i, cost μ caps i+(Fintype.card I:ℝ)/10 ∧
--         (∑ S ∈ P.parts, Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
--         (∑ S ∈ P.parts, Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T))) ≤
--           C*((Fintype.card I:ℝ)+∑ i,cost μ caps i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlockGeometry.radius`, `OAI.BlockSets.clipped`, `OAI.BlockSets.common`, `OAI.BlockSets.cost` and `OAI.Blocks.weight` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.WitnessConstruction.shell` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/Blocks.lean (declaration OAI.Blocks.block_estimates)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace Blocks
universe u₁ u₂
open Finset MeasureTheory BlockGeometry BlockSets
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

theorem block_estimates {L C0 c0 : ℝ} (hL : 1 ≤ L) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) :
    ∃ B K C : ℝ, 0 < B ∧ 0 < K ∧ 0 < C ∧
    ∀ (Ω : Type u₁) (I : Type u₂) [MeasurableSpace Ω] [StandardBorelSpace Ω]
      [Fintype I] [Nonempty I] [DecidableEq I] (μ : Measure Ω)
      [IsFiniteMeasure μ] [NullSingletonClass μ],
    ∀ (u : ℝ), 1 ≤ u → (Fintype.card I:ℝ) ≤ Real.exp (2*u) →
    ∀ (caps : I → Set Ω), (∀ i, MeasurableSet (caps i)) → (∀ i, 0 < μ.real (caps i)) →
    ∀ (d : I → I → ℝ), (∀ i j, 0 ≤ d i j) → (∀ i, d i i = 0) →
      (∀ i j, d i j = d j i) → (∀ i j k, d i k ≤ d i j+d j k) →
    (∀ i j, μ.real (caps i ∩ caps j)/Real.sqrt (clipped μ caps i*clipped μ caps j) ≤
      C0*Real.exp (-c0*d i j^2)) →
    (∀ S : Finset I, S.Nonempty → radius d S ≤ B*u →
      ∀ a ∈ S, (∀ i ∈ S, μ.real (caps a) ≤ μ.real (caps i)) →
      Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ caps a ≤ μ.real (common caps S)) →
    ∃ (P : Finpartition (univ : Finset I)) (a : Finset I → I) (E : Finset I → Set Ω),
      (∀ S ∈ P.parts, a S ∈ S ∧ (∀ i ∈ S, μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
        MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        Real.exp (-K*u)*clipped μ caps (a S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      (∑ S ∈ P.parts, -Real.log (μ.real (E S))) ≤ ∑ i, cost μ caps i+(Fintype.card I:ℝ)/10 ∧
      (∑ S ∈ P.parts, Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
      (∑ S ∈ P.parts, Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T))) ≤
        C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) := by
  sorry

end Blocks

end OAI
end
