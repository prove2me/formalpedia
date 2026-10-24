-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_le_of_real_lower_bound_408915f
-- name    : FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:26.45999+00:00
-- url     : https://prove2.me/theorems/641ca0ec-b76f-42d4-a0a7-98fc01c98c7f
-- title:
--   Legendre Upper Bound from a Bounded Domain and Real Floor
-- statement:
--   This bounds the actual extended-real Legendre transform using a bounded effective domain.
--
--   Let $\phi:E\to\overline{\mathbb R}$, let $L\in[0,\infty)$, and let $m\in\mathbb R$. Assume:
--
--   1. $\phi(y)\neq-\infty$ for every $y$;
--   2. if $\phi(y)\neq+\infty$, then $\|y\|\leq L$;
--   3. $m\leq\phi(y)$ for every $y$.
--
--   Then for every $x\in E$,
--
--   $$
--   \operatorname{Leg}(\phi)(x)
--   \leq
--   L\|x\|-m,
--   $$
--
--   with the right-hand side coerced into `EReal`. The statement controls the full extended-real supremum and does not assume finite dimensionality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L104-L136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_408915f
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
    legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by sorry
