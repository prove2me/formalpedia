-- Prove2me | Theorems.Thm_OAI_PoissonBinned_bound
-- name    : OAI.PoissonBinned.bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:44:26.888984+00:00
-- url     : https://prove2.me/theorems/c064eaad-3e3c-42d5-9dd1-5995d27496af
-- title:
--   OAI.PoissonBinned.bound: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PoissonBinned.bound` of [lean/OAI/Geometry/TranslativeCovering/PoissonBinned.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PoissonBinned.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PoissonBinned`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Finset MeasureTheory PoissonConfig PoissonDiagrams`, `open scoped BigOperators ENNReal NNReal`):
--
--   ```lean
--   theorem bound (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] [NullSingletonClass σ]
--       (E : ∀ t,I t → Set Ω) (hE : ∀ t i,MeasurableSet (E t i))
--       (hpos : ∀ t i,0 < (((r:ℝ≥0∞) • σ).real (E t i)))
--       (bad : T → T → Prop) [DecidableRel bad] {a q f g B : ℝ}
--       (ha : 0 < a) (hf : 0 ≤ f) (hg : 0 ≤ g)
--       (hbin : ∀ t,a ≤ (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ∧
--         (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ≤ 2*a)
--       (hself : ∀ t,diagram ((r:ℝ≥0∞) • σ) (E t) (E t) ≤
--         (∏ i,((r:ℝ≥0∞) • σ).real (E t i))^2*Real.exp B)
--       (hcross : ∀ t u,t ≠ u → diagram ((r:ℝ≥0∞) • σ) (E t) (E u) ≤
--         if bad t u then g*(∏ i,((r:ℝ≥0∞) • σ).real (E t i))*(∏ j,((r:ℝ≥0∞) • σ).real (E u j)) else 0)
--       (hbad : (((univ : Finset (T×T)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card:ℝ) ≤
--         10*f*q^2*(Fintype.card T:ℝ)^2) :
--       (PoissonSample.simpleSample r σ).real {x | ∀ t,witnessCount (E t) x = 0} ≤
--         Real.exp (-1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*g*q^2*f)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PoissonConfig.Config`, `OAI.PoissonConfig.witnessCount`, `OAI.PoissonDiagrams.diagram` and `OAI.PoissonSample.simpleSample` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.PatternTail.bound` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PoissonBinned.lean (declaration OAI.PoissonBinned.bound)

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
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonBinned
open Set Finset MeasureTheory PoissonConfig PoissonDiagrams
open scoped BigOperators ENNReal NNReal
variable {Ω : Type u_1} {T : Type u_2} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [Fintype T] [Nonempty T] [DecidableEq T] {I : T → Type u_3}
variable [∀ t,Fintype (I t)] [∀ t,Nonempty (I t)]

theorem bound (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] [NullSingletonClass σ]
    (E : ∀ t,I t → Set Ω) (hE : ∀ t i,MeasurableSet (E t i))
    (hpos : ∀ t i,0 < (((r:ℝ≥0∞) • σ).real (E t i)))
    (bad : T → T → Prop) [DecidableRel bad] {a q f g B : ℝ}
    (ha : 0 < a) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hbin : ∀ t,a ≤ (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ∧
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ≤ 2*a)
    (hself : ∀ t,diagram ((r:ℝ≥0∞) • σ) (E t) (E t) ≤
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i))^2*Real.exp B)
    (hcross : ∀ t u,t ≠ u → diagram ((r:ℝ≥0∞) • σ) (E t) (E u) ≤
      if bad t u then g*(∏ i,((r:ℝ≥0∞) • σ).real (E t i))*(∏ j,((r:ℝ≥0∞) • σ).real (E u j)) else 0)
    (hbad : (((univ : Finset (T×T)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card:ℝ) ≤
      10*f*q^2*(Fintype.card T:ℝ)^2) :
    (PoissonSample.simpleSample r σ).real {x | ∀ t,witnessCount (E t) x = 0} ≤
      Real.exp (-1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*g*q^2*f))) := by
  sorry

end PoissonBinned

end OAI
end
