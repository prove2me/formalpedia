-- Prove2me | Theorems.Thm_OAI_CapGeometry_halfcap_ratio
-- name    : OAI.CapGeometry.halfcap_ratio
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:43:31.459985+00:00
-- url     : https://prove2.me/theorems/6676dbfd-625c-4a47-ae74-ea9177915cd8
-- title:
--   OAI.CapGeometry.halfcap_ratio: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CapGeometry.halfcap_ratio` of [lean/OAI/Geometry/TranslativeCovering/CapGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CapGeometry`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set MeasureTheory Metric`, `open scoped ENNReal Pointwise`, `open SphericalLaw`):
--
--   ```lean
--   lemma halfcap_ratio {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
--       (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
--       Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(s-t)) ≤
--         (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ∧
--       (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ≤
--         Real.exp (((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapGeometry.halfcap`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.σ` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proofs of `OAI.CapCost.clipped_cost`, `OAI.CapCost.raw_upper`, `OAI.CapOverlap.cap_ratio_decay`, `OAI.LensDeployment.tangent_bad_vector` and `OAI.RadiusLens.lens_at_radius` of this split import it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/CapGeometry.lean (declaration OAI.CapGeometry.halfcap_ratio)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
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

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

lemma halfcap_ratio {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
    Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(s-t)) ≤
      (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ∧
    (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ≤
      Real.exp (((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t)) := by
  sorry

end CapGeometry

end OAI
end
