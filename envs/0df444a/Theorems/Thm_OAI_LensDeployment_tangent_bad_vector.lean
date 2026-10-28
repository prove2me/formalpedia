-- Prove2me | Theorems.Thm_OAI_LensDeployment_tangent_bad_vector
-- name    : OAI.LensDeployment.tangent_bad_vector
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:43:23.428028+00:00
-- url     : https://prove2.me/theorems/427d9318-8410-4ff5-bb29-24b09a6f0034
-- title:
--   OAI.LensDeployment.tangent_bad_vector: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LensDeployment.tangent_bad_vector` of [lean/OAI/Geometry/TranslativeCovering/LensDeployment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/LensDeployment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LensDeployment`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens CapCost CapAffinity`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   lemma tangent_bad_vector {n : ℕ} [NeZero n] (e : Sphere n) (v : Space n)
--       (hev : inner ℝ e.val v = 0) {l u t h Φ : ℝ}
--       (hΦ : ‖v‖ ≤ Φ) (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
--       (hqu : Real.sqrt (t^2+h^2) ≤ u)
--       (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
--       (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h}) ≤
--         Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CapGeometry.halfcap`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.σ` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.RadiusLens.lens_at_radius` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/LensDeployment.lean (declaration OAI.LensDeployment.tangent_bad_vector)

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

universe u_1 u_2

namespace LensDeployment
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens CapCost CapAffinity
open scoped ENNReal NNReal

lemma tangent_bad_vector {n : ℕ} [NeZero n] (e : Sphere n) (v : Space n)
    (hev : inner ℝ e.val v = 0) {l u t h Φ : ℝ}
    (hΦ : ‖v‖ ≤ Φ) (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h}) ≤
      Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
  sorry

end LensDeployment

end OAI
end
