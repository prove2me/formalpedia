-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_density_moment_equiv
-- name    : OAI.ProjectionMoments.density_moment_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:50:12.099742+00:00
-- url     : https://prove2.me/theorems/09e04e9a-30c2-4764-8ce8-0495370793e1
-- title:
--   Moments of densities under a measure-scaling transformation
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure and $e$ a measurable bijection with $e_*\mu=c\,\mu$ for a constant $0<c<\infty$. If the measurable densities $f,g$ satisfy $e_*(f\mu)=g\mu$, then for every $n$,
--   $$
--   \int g^{n+1}\,d\mu=c^{\,n}\int f^{n+1}\,d\mu .
--   $$
--
--   It is used to transport moments of densities under rotations and rescalings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/GaussianDensity.lean#L148-L176

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem OAI.ProjectionMoments.density_moment_equiv {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : X ≃ᵐ X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : μ.map e = c • μ) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : (μ.withDensity f).map e = μ.withDensity g) (n : ℕ) :
    ∫⁻ y, g y ^ (n+1) ∂μ = c^n * ∫⁻ x, f x ^ (n+1) ∂μ := by sorry
