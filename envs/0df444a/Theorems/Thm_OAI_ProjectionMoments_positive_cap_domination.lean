-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_positive_cap_domination
-- name    : OAI.ProjectionMoments.positive_cap_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:21:08.492132+00:00
-- url     : https://prove2.me/theorems/fcac0918-ee0c-4830-869e-ef985a295385
-- title:
--   Domination of cap kernels by a cheap combination of caps
-- statement:
--   Let $\sigma$ be the normalized surface measure on the unit sphere of $\mathbb R^d$ and $\sigma_{c,r}$ the cap measure ($\sigma$ restricted to $\bar B(c,r)$, normalized to mass one). For a kernel $K(X,z)$ with $X\in(\mathbb R^d)^k$ and $z\in\mathbb R^k$, the cap kernel value is $\kappa_K(s)=\int K\bigl(X,(\langle s,X_i\rangle)_i\bigr)\,d\gamma^{\otimes k}(X)$, where $\gamma$ is the standard Gaussian. The cap reference is $\mathrm{ref}_K(c,r)=\int\!\!\int K\bigl(X,P_Xc+r\,R_Xz\bigr)\,d\beta_k(z)\,d\gamma^{\otimes k}(X)$, where $P_X$ is the projection onto the rows of $X$, $R_X$ is the radial factor of the polar decomposition of $X$, and $\beta_k$ is the uniform law on the unit ball of $\mathbb R^k$. There is $C>0$ such that for all $d\ge32$, with $k=\lfloor d/16\rfloor$ and $\alpha=(d-1)/2$, the following holds. For every unit $c$, $0<r\le2$ and measurable $K$ with $0\le K\le1$, there are a cap dictionary $(c_i,\rho_i)$ for $(c,r,\alpha)$ and coefficients $a_i\ge0$ such that the measure $\sum_ia_i\sigma_{c_i,\rho_i}$ is finite,
--   $$
--   \sum_ia_i\Bigl(\frac r{\rho_i}\Bigr)^\alpha\le e^{Cd}\,\mathrm{ref}_K(c,r)^{1-1/k}\qquad\text{and}\qquad\kappa_K\,\sigma_{c,r}\le\sum_ia_i\,\sigma_{c_i,\rho_i},
--   $$
--   with the series $\sum_ia_i(r/\rho_i)^\alpha$ summable.
--
--   So the kernel-weighted cap measure is covered by smaller caps at a cost controlled by the cap reference.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapDomination.lean#L11-L70

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
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem OAI.ProjectionMoments.positive_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue K) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by sorry
