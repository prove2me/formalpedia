-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_quadraticExponent_concave_408915f
-- name    : FunctionalInequalities.Probability.Posterior.quadraticExponent_concave_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:08:00.880476+00:00
-- url     : https://prove2.me/theorems/2f84177e-afc4-4c11-9fac-7140cbb79f47
-- title:
--   Concavity of the Linear–Quadratic Posterior Exponent
-- statement:
--   This statement establishes concavity of the linear–quadratic exponent used for posterior tilting.
--
--   Let $E$ be a real inner-product space, $c\in E$, and $Q:E\to E$ a continuous linear map. Assume:
--
--   1. $Q$ is symmetric: $\langle Qu,v\rangle=\langle u,Qv\rangle$ for all $u,v\in E$.
--   2. $Q$ is positive semidefinite: $\langle Qx,x\rangle\ge0$ for every $x\in E$.
--
--   For `quadraticExponent` defined by
--
--   $$
--   \operatorname{quadraticExponent}(c,Q)(x)=\langle c,x\rangle-\frac12\langle Qx,x\rangle,
--   $$
--
--   this function is concave on all of $E$:
--
--   $$
--   \operatorname{ConcaveOn}(\mathbb{R},E,\operatorname{quadraticExponent}(c,Q)).
--   $$
--
--   The result supplies the concavity condition needed to show that the associated linear–quadratic posterior is log-concave.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean#L57-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Exponent`, declaration `FunctionalInequalities.Probability.Posterior.quadraticExponent_concave`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open Set

theorem FunctionalInequalities.Probability.Posterior.quadraticExponent_concave_408915f (c : E) (Q : E →L[ℝ] E)
    (hSym : ∀ u v : E, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : ConcaveOn ℝ univ (quadraticExponent c Q) := by sorry
