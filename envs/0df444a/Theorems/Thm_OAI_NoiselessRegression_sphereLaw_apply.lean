-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_sphereLaw_apply
-- name    : OAI.NoiselessRegression.sphereLaw_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:31:36.921172+00:00
-- url     : https://prove2.me/theorems/9c34a358-deab-414f-8cea-f675049931fc
-- title:
--   The uniform sphere measure is the uniform ball measure of the cone over a set
-- statement:
--   Let $E$ be a nontrivial real inner product space of finite dimension $d\ge1$ with Lebesgue (Haar) measure $\mathrm{Vol}$, and let $\mathbb S=\{x\in E:\|x\|=1\}$ be its unit sphere. For $s\subseteq\mathbb S$ write $(0,1)\cdot s=\{rx:0<r<1,\ x\in s\}$ for the open cone over $s$ truncated at radius $1$. Consider two probability measures:
--
--   1. the uniform ball law $\beta=\mathrm{Vol}(B(0,1))^{-1}\,\mathrm{Vol}|_{\bar B(0,1)}$, i.e. normalized Lebesgue measure on the closed unit ball;
--   2. the uniform sphere law $\sigma$, the normalization to total mass $1$ of Mathlib's surface measure on $\mathbb S$ induced by $\mathrm{Vol}$, which assigns to a measurable $s\subseteq\mathbb S$ the mass $d\cdot\mathrm{Vol}\big((0,1)\cdot s\big)$.
--
--   Then for every measurable $s\subseteq\mathbb S$,
--
--   $$
--   \sigma(s)=\beta\big((0,1)\cdot s\big)=\frac{\mathrm{Vol}\big(\{rx:0<r<1,\ x\in s\}\big)}{\mathrm{Vol}\big(B(0,1)\big)}.
--   $$
--
--   This identifies the uniform measure on the sphere as the cone measure: the mass of a set of directions is the fraction of the unit ball swept out by the corresponding open cone. It reduces statements about the sphere, such as cap bounds and invariance under linear isometries, to statements about Lebesgue measure on the ball.
--
--   **Formalization Note** The sphere is a subtype of $E$, $s$ is a set of points of that subtype, and $(0,1)\cdot s$ is the pointwise product of the interval with the image of $s$ in $E$. The surface measure is `Measure.toSphere`, $\sigma$ is `sphereLaw` and $\beta$ is `unitBallLaw`. Nontriviality of $E$ ensures $d\ge1$, so that the factor $d$ can be cancelled.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean#L66-L86

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

theorem OAI.NoiselessRegression.sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by sorry
