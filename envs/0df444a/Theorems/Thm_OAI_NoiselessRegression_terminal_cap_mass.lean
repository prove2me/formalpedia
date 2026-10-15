-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_terminal_cap_mass
-- name    : OAI.NoiselessRegression.terminal_cap_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:33:33.687525+00:00
-- url     : https://prove2.me/theorems/12209744-378e-4d4f-afef-b4f90855769a
-- title:
--   Uniform sphere measure of the intersection of two balls
-- statement:
--   Let $E$ be a nontrivial real inner product space of finite dimension $d\ge1$, and let $\bar\sigma$ be the uniform probability measure on the unit sphere of $E$, viewed as a Borel measure on $E$ (the image under the inclusion of the normalized surface measure, which gives a set $s$ of unit vectors the mass $\mathrm{Vol}(\{rx:0<r<1,\ x\in s\})/\mathrm{Vol}(B(0,1))$). Let $y,z\in E$, let $\varepsilon>0$ and $r>0$, and let $a\in\mathbb N$ satisfy $2a\le d-1$. Then
--
--   $$
--   \bar\sigma\big(\bar B(y,\varepsilon)\cap\bar B(z,r)\big)\;\le\;3\cdot4^{d}\,\varepsilon^{a}\,r^{a}.
--   $$
--
--   Equivalently, the restriction of $\bar\sigma$ to the closed ball $\bar B(y,\varepsilon)$ satisfies the polynomial mass bound $\bar\sigma|_{\bar B(y,\varepsilon)}\big(\bar B(z,r)\big)\le\big(3\cdot4^d\varepsilon^{a}\big)\,r^{a}$ at every centre $z$ and radius $r$, with a constant that is small when the cap $\bar B(y,\varepsilon)$ is small. This is the form in which a small target cap around the unknown direction enters estimates that require a polynomial mass bound.
--
--   **Formalization Note** The left-hand side is written in Lean as the restricted measure `ambientSphereLaw.restrict (closedBall y ε)` evaluated on `closedBall z r`, and $d-1$ is natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean#L159-L179

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

theorem OAI.NoiselessRegression.terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by sorry
