-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_projectionLaw_absolutelyContinuous
-- name    : OAI.NoiselessRegression.projectionLaw_absolutelyContinuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:36:11.649614+00:00
-- url     : https://prove2.me/theorems/5098e1e5-a245-4c8b-821a-202f2d2647ef
-- title:
--   Gaussian projections of measures with polynomial mass are absolutely continuous
-- statement:
--   Let $\nu$ be a finite measure supported in the closed unit ball of a finite-dimensional inner product space, with polynomial mass $\nu(\bar B(z,r))\le Cr^a$ for all balls, $0<C<\infty$. If $m+n\le a$ for some $n\ge1$, then the law of $m$ Gaussian rows together with the noiseless labels $y_j=\langle t,A_j\rangle$, $t\sim\nu$, is absolutely continuous with respect to Gaussian rows times Lebesgue measure on labels:
--   $$
--   \mathrm{law}(A,y)\ll\gamma^{\otimes m}\otimes\mathrm{Leb}_m .
--   $$
--
--   This guarantees that the projected densities used in the moment bounds exist.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Observation.lean#L25-L50

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by sorry
