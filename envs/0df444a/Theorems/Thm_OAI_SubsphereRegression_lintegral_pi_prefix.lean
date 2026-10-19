-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_lintegral_pi_prefix
-- name    : OAI.SubsphereRegression.lintegral_pi_prefix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:35:27.480978+00:00
-- url     : https://prove2.me/theorems/1e7b28ef-b1b7-4f79-8104-45d645d20f3b
-- title:
--   Integrals of functions of the first $t$ coordinates under a product probability measure
-- statement:
--   Let $E$ be a measurable space and $\nu$ a probability measure on $E$, and write $\nu^{\otimes T}$ for the product measure on $E^T$. Let $t\le T$ be natural numbers and let $f:E^t\to[0,\infty]$ be measurable. Then
--
--   $$
--   \int_{E^T}f(x_1,\dots,x_t)\,d\nu^{\otimes T}(x)=\int_{E^t}f(x)\,d\nu^{\otimes t}(x).
--   $$
--
--   In other words, the image of $\nu^{\otimes T}$ under the projection $(x_1,\dots,x_T)\mapsto(x_1,\dots,x_t)$ onto the first $t$ coordinates is $\nu^{\otimes t}$. This marginalization identity lets one evaluate events depending only on an initial segment of an i.i.d. sample (for instance, the state of a streaming algorithm after its first $t$ observations) by integrating over the shorter sample only.
--
--   **Formalization Note** Tuples are indexed by `Fin T`, and the first $t$ coordinates are taken through `Fin.castLE`. The integrals are lower Lebesgue integrals; no structure on $E$ beyond its $\sigma$-algebra is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L204-L228

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem OAI.SubsphereRegression.lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by sorry
