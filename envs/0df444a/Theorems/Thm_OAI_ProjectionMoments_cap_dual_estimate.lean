-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_cap_dual_estimate
-- name    : OAI.ProjectionMoments.cap_dual_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:15:50.137798+00:00
-- url     : https://prove2.me/theorems/12ce51b5-a99d-4581-83ea-d556b57dcb17
-- title:
--   Dual estimate for cap kernels against cap-bounded weights
-- statement:
--   Let $\sigma$ be the normalized surface measure on the unit sphere of $\mathbb R^d$ and $\sigma_{c,r}$ the cap measure ($\sigma$ restricted to $\bar B(c,r)$, normalized to mass one). For a kernel $K(X,z)$ with $X\in(\mathbb R^d)^k$ and $z\in\mathbb R^k$, the cap kernel value is $\kappa_K(s)=\int K\bigl(X,(\langle s,X_i\rangle)_i\bigr)\,d\gamma^{\otimes k}(X)$, where $\gamma$ is the standard Gaussian. The cap reference is $\mathrm{ref}_K(c,r)=\int\!\!\int K\bigl(X,P_Xc+r\,R_Xz\bigr)\,d\beta_k(z)\,d\gamma^{\otimes k}(X)$, where $P_X$ is the projection onto the rows of $X$, $R_X$ is the radial factor of the polar decomposition of $X$, and $\beta_k$ is the uniform law on the unit ball of $\mathbb R^k$. There is $C>0$ such that for all $d\ge32$, with $k=\lfloor d/16\rfloor$ and $\alpha=(d-1)/2$, the following holds. Let $\|c\|=1$ and $0<r\le2$, let $(c_i,\rho_i)$ be a cap dictionary for $(c,r,\alpha)$, and let $K$ be measurable with $0\le K\le1$. If a measurable $h\ge0$ satisfies $\int h\,d\sigma_{c_i,\rho_i}\le(r/\rho_i)^\alpha$ for every $i$, then
--   $$
--   \int h\,\kappa_K\,d\sigma_{c,r}\le e^{Cd}\,\mathrm{ref}_K(c,r)^{1-1/k}.
--   $$
--
--   This is the dual form of the cap domination estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapDuality.lean#L149-L203

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem OAI.ProjectionMoments.cap_dual_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ D : CapDictionary c r α,
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) →
      (∫⁻ s, h s*capKernelValue K s ∂capMeasure c r) ≤
        ENNReal.ofReal (Real.exp (C*d)) * (capReference K c r)^(1-1/(k:ℝ)) := by sorry
