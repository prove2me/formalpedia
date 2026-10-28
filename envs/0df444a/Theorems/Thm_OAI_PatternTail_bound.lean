-- Prove2me | Theorems.Thm_OAI_PatternTail_bound
-- name    : OAI.PatternTail.bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:44:18.6024+00:00
-- url     : https://prove2.me/theorems/d88c3e1e-833a-4e64-8ed2-49c7e5e38b1a
-- title:
--   OAI.PatternTail.bound: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PatternTail.bound` of [lean/OAI/Geometry/TranslativeCovering/PatternTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PatternTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PatternTail`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Metric MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness PoissonDiagrams`, `open scoped BigOperators ENNReal Classical`):
--
--   ```lean
--   theorem bound {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
--       (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
--       ∃ K A H : ℝ,0 < K ∧ 0 < A ∧ 0 < H ∧ ∃ n₀ : ℕ,
--       ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
--       ∀ (J : Type u_3) [Fintype J] [Nonempty J] (e : Sphere n) (p : J → Space n)
--         (D C ε : ℝ) (M : ℕ),
--       0 < D → 0 ≤ C → C ≤ (n:ℝ)^2 → 0 < ε → ε ≤ 1 → 2 ≤ M →
--       0 < RadialShell.low a n →
--       1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n →
--       volume (closedBall (0 : Space n) D) ≤ 4*volume
--         (roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C) →
--       ((TargetSampling.pairs M).card:ℝ)*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
--         (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 →
--       (BodyVolume.law e a).real (coverEvent p a D) ≤
--         Real.exp (-1/(8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+
--           10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*
--             (12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
--               (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ActivityBins.count`, `OAI.BodyVolume.law`, `OAI.PatternGeometry.Space`, `OAI.PatternGeometry.roundedGood`, `OAI.PatternTail.Space`, `OAI.PatternTail.coverEvent`, `OAI.PoissonConfig.Config`, `OAI.RadialShell.high`, `OAI.RadialShell.low`, `OAI.RadialShell.η`, `OAI.SphericalLaw.Space` and `OAI.SphericalLaw.Sphere` (definitions bundle `OAIQ16Cd000` of this split); `OAI.TargetSampling.pairs` (definitions bundle `OAIQ16Cd001` of this split).
--
--   **Used by.** The proof of `OAI.SourcePatternTail.uniform` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PatternTail.lean (declaration OAI.PatternTail.bound)

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Definitions.Def_OAIQ16Cd001

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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternTail
open Set Metric MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness PoissonDiagrams
open scoped BigOperators ENNReal Classical

theorem bound {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
    ∃ K A H : ℝ,0 < K ∧ 0 < A ∧ 0 < H ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (J : Type u_3) [Fintype J] [Nonempty J] (e : Sphere n) (p : J → Space n)
      (D C ε : ℝ) (M : ℕ),
    0 < D → 0 ≤ C → C ≤ (n:ℝ)^2 → 0 < ε → ε ≤ 1 → 2 ≤ M →
    0 < RadialShell.low a n →
    1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n →
    volume (closedBall (0 : Space n) D) ≤ 4*volume
      (roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C) →
    ((TargetSampling.pairs M).card:ℝ)*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
      (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 →
    (BodyVolume.law e a).real (coverEvent p a D) ≤
      Real.exp (-1/(8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+
        10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*
          (12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
            (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))))) := by
  sorry
end PatternTail

end OAI
end
