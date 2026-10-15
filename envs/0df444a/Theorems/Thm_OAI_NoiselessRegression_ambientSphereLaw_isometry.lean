-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_ambientSphereLaw_isometry
-- name    : OAI.NoiselessRegression.ambientSphereLaw_isometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:35:00.643826+00:00
-- url     : https://prove2.me/theorems/66d4f294-da52-4439-82ab-8f818f39dbdb
-- title:
--   Linear isometries preserve the uniform measure on the sphere
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $\bar\sigma$ be the uniform probability measure on the unit sphere $\mathbb S=\{x:\|x\|=1\}$, viewed as a Borel measure on $E$. Here $\bar\sigma$ is the image under the inclusion $\mathbb S\hookrightarrow E$ of the normalized surface measure, which gives a measurable set $s\subseteq\mathbb S$ the mass $\mathrm{Vol}(\{rx:0<r<1,\ x\in s\})/\mathrm{Vol}(B(0,1))$. Then every linear isometric isomorphism $e:E\to E$ is measurable and preserves $\bar\sigma$:
--
--   $$
--   \bar\sigma\big(e^{-1}(B)\big)=\bar\sigma(B)\qquad\text{for every Borel set }B\subseteq E,
--   $$
--
--   that is, $e_{\#}\bar\sigma=\bar\sigma$.
--
--   This is the rotation and reflection invariance of the uniform distribution on the sphere. It is used, for instance, to show that $\int\langle v,x\rangle^2\,d\bar\sigma(x)=1/d$ for every unit vector $v$ (where $d=\dim E$), and that reflections in subspaces preserve the uniform distribution of an unknown direction.
--
--   **Formalization Note** In Lean, $e$ is a linear isometry equivalence `E ≃ₗᵢ[ℝ] E`, and the conclusion is `MeasurePreserving e ambientSphereLaw ambientSphereLaw`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean#L224-L242

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by sorry
