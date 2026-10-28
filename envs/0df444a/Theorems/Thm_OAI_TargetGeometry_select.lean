-- Prove2me | Theorems.Thm_OAI_TargetGeometry_select
-- name    : OAI.TargetGeometry.select
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:46.811539+00:00
-- url     : https://prove2.me/theorems/51c2b706-9de8-4d85-9f70-d22ea6d15c69
-- title:
--   OAI.TargetGeometry.select: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TargetGeometry.select` of [lean/OAI/Geometry/TranslativeCovering/TargetGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/TargetGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TargetGeometry`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set MeasureTheory Metric CylinderProbability ConeStretch`, `open scoped ENNReal`):
--
--   ```lean
--   theorem select {n : ℕ} [NeZero n] {I : Type u_4} [Fintype I]
--       (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
--       {D L t ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (ht : 0 < t) (hξ : 0 < ξ)
--       (hGsub : G ⊆ closedBall (0 : Space n) D)
--       (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
--       {M : ℕ} (hM : 2 ≤ M) (hI : Nonempty I)
--       (hsmall : ((TargetSampling.pairs M).card:ℝ)*
--         (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*t/D)^(n-1)) < 1/2) :
--       ∃ x : Fin M → Space n, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
--         (∀ i j,i ≠ j → (x i,x j) ∉ bad p L t) ∧
--         TargetSampling.score (bad p L ξ) x ≤
--           10*((TargetSampling.pairs M).card:ℝ)*
--             (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ConeStretch.Space` (definitions bundle `OAIQ16Cd000` of this split); `OAI.TargetSampling.pairs` and `OAI.TargetSampling.score` (definitions bundle `OAIQ16Cd001` of this split); `OAI.TargetGeometry.bad` (definitions bundle `OAIQ16Cd002` of this split).
--
--   **Used by.** The proof of `OAI.PatternTail.bound` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/TargetGeometry.lean (declaration OAI.TargetGeometry.select)

import Mathlib
import Definitions.Def_OAIQ16Cd002

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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace TargetGeometry
open Set MeasureTheory Metric CylinderProbability ConeStretch
open scoped ENNReal

theorem select {n : ℕ} [NeZero n] {I : Type u_4} [Fintype I]
    (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
    {D L t ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (ht : 0 < t) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    {M : ℕ} (hM : 2 ≤ M) (hI : Nonempty I)
    (hsmall : ((TargetSampling.pairs M).card:ℝ)*
      (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*t/D)^(n-1)) < 1/2) :
    ∃ x : Fin M → Space n, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
      (∀ i j,i ≠ j → (x i,x j) ∉ bad p L t) ∧
      TargetSampling.score (bad p L ξ) x ≤
        10*((TargetSampling.pairs M).card:ℝ)*
          (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1)) := by
  sorry

end TargetGeometry

end OAI
end
