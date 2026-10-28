-- Prove2me | Theorems.Thm_OAI_PatternCross_fine
-- name    : OAI.PatternCross.fine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:02.452739+00:00
-- url     : https://prove2.me/theorems/1619b711-04f0-4001-bd49-27be2de83c78
-- title:
--   OAI.PatternCross.fine: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PatternCross.fine` of [lean/OAI/Geometry/TranslativeCovering/PatternCross.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PatternCross.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PatternCross`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams`, `open scoped BigOperators`):
--
--   ```lean
--   theorem fine {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
--       (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
--       ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
--       ∀ {J : Type u_2} [Fintype J] (e : Sphere n) (p : J → Space n) (x y : Space n) (D A C : ℝ),
--       0 < RadialShell.low a n →
--       x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
--       y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
--       (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (H*Real.sqrt (Real.log n/(n:ℝ))) →
--       ∀ (W : Certificate e p x a K A C) (V : Certificate e p y a K A C),
--       diagram (intensity e (1/a)) W.slot V.slot ≤ (n:ℝ)⁻¹^3*activity W*activity V
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapCost.intensity`, `OAI.ConeStretch.Space`, `OAI.PatternCross.Space`, `OAI.PatternCross.activity`, `OAI.PatternGeometry.Space`, `OAI.PatternGeometry.relevant`, `OAI.PatternGeometry.roundedGood`, `OAI.PatternWitness.Certificate`, `OAI.PoissonDiagrams.diagram`, `OAI.RadialShell.high`, `OAI.RadialShell.low`, `OAI.SphericalLaw.Space` and `OAI.SphericalLaw.Sphere` (definitions bundle `OAIQ16Cd000` of this split); `OAI.TargetGeometry.bad` (definitions bundle `OAIQ16Cd002` of this split).
--
--   **Used by.** The proof of `OAI.PatternTail.bound` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PatternCross.lean (declaration OAI.PatternCross.fine)

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

universe u_1 u_2 u_3

namespace PatternCross
open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams
open scoped BigOperators

theorem fine {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
    ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ {J : Type u_2} [Fintype J] (e : Sphere n) (p : J → Space n) (x y : Space n) (D A C : ℝ),
    0 < RadialShell.low a n →
    x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (H*Real.sqrt (Real.log n/(n:ℝ))) →
    ∀ (W : Certificate e p x a K A C) (V : Certificate e p y a K A C),
    diagram (intensity e (1/a)) W.slot V.slot ≤ (n:ℝ)⁻¹^3*activity W*activity V := by
  sorry

end PatternCross

end OAI
end
