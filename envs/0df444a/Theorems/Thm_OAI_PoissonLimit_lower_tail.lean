-- Prove2me | Theorems.Thm_OAI_PoissonLimit_lower_tail
-- name    : OAI.PoissonLimit.lower_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:45:13.737146+00:00
-- url     : https://prove2.me/theorems/97a81da2-d769-4bd5-82b3-0a159b24f27c
-- title:
--   OAI.PoissonLimit.lower_tail: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PoissonLimit.lower_tail` of [lean/OAI/Geometry/TranslativeCovering/PoissonLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PoissonLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PoissonLimit`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams`, `open scoped Classical BigOperators ENNReal`):
--
--   ```lean
--   theorem lower_tail [StandardBorelSpace Ω] (μ : Measure Ω)
--       [IsFiniteMeasure μ] [NullSingletonClass μ]
--       (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
--       (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i))
--       (hpos : ∀ a i, 0 < μ.real (E a i)) :
--       (0 < ∑ a, ∑ b, diagram μ (E a) (E b)) ∧
--       P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
--         (-(∑ a, ∏ i, μ.real (E a i))^2 /
--           (2 * (∑ a, ∑ b, diagram μ (E a) (E b))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PoissonConfig.Config`, `OAI.PoissonConfig.HasVoidLaw`, `OAI.PoissonConfig.witnessCount` and `OAI.PoissonDiagrams.diagram` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.PoissonBinned.bound` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/PoissonLimit.lean (declaration OAI.PoissonLimit.lower_tail)

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

namespace PoissonLimit
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators ENNReal
variable {Ω : Type u_1} {A : Type u_2} [MeasurableSpace Ω] [Fintype A] [Nonempty A]
variable {I : A → Type u_3} [∀ a, Fintype (I a)] [∀ a, Nonempty (I a)]

theorem lower_tail [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i))
    (hpos : ∀ a i, 0 < μ.real (E a i)) :
    (0 < ∑ a, ∑ b, diagram μ (E a) (E b)) ∧
    P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, ∏ i, μ.real (E a i))^2 /
        (2 * (∑ a, ∑ b, diagram μ (E a) (E b)))) := by
  sorry

end PoissonLimit

end OAI
end
