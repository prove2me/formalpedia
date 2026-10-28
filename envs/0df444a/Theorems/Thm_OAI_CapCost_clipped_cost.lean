-- Prove2me | Theorems.Thm_OAI_CapCost_clipped_cost
-- name    : OAI.CapCost.clipped_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:42:36.01393+00:00
-- url     : https://prove2.me/theorems/b25b4444-1b9a-46ff-a8f4-2c13c844e57c
-- title:
--   OAI.CapCost.clipped_cost: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CapCost.clipped_cost` of [lean/OAI/Geometry/TranslativeCovering/CapCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CapCost`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open MeasureTheory SphericalLaw CapGeometry CapAffinity`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   lemma clipped_cost {n : ℕ} [NeZero n] (e f : Sphere n) {l u t s : ℝ}
--       (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
--       (hls : l ≤ s) (hsu : s ≤ u) :
--       -Real.log (min ((intensity e t).real (cap f.val s)) (1/2)) ≤
--         Real.log 2+(n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapCost.intensity`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.cap` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proofs of `OAI.PatternCross.fine` and `OAI.WitnessConstruction.shell` of this split import it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapCost.lean (declaration OAI.CapCost.clipped_cost)

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

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

lemma clipped_cost {n : ℕ} [NeZero n] (e f : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (hls : l ≤ s) (hsu : s ≤ u) :
    -Real.log (min ((intensity e t).real (cap f.val s)) (1/2)) ≤
      Real.log 2+(n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0 := by
  sorry

end CapCost

end OAI
end
