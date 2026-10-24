-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_real_global_minimum_of_bounded_domain_408915f
-- name    : FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:20.969341+00:00
-- url     : https://prove2.me/theorems/8a31a290-7933-457a-a867-0b12f79aae6a
-- title:
--   Finite Real Minimum on a Bounded Effective Domain
-- statement:
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$, and let $L\in[0,\infty)$. Assume $\phi(y)\ne-\infty$ for every $y$, some value of $\phi$ is finite, $\phi$ is lower semicontinuous, and every point where $\phi(y)\ne+\infty$ lies in the closed ball $\overline B(0,L)$. Then there exist $a\in\overline B(0,L)$ and $m\in\mathbb R$ such that
--
--   $$\phi(a)=m\quad\text{and}\quad m\le\phi(y)\ \text{for every }y\in E.$$
--
--   The conclusion explicitly produces a real-valued global minimum after excluding both extended-real infinities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L69-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain`; the repository is private at upload time).

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
omit [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_408915f
    (φ : E → EReal) (L : NNReal)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hlsc : LowerSemicontinuous φ)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) :
    ∃ a ∈ closedBall (0 : E) (L : ℝ), ∃ m : ℝ,
      φ a = (m : EReal) ∧ ∀ y, (m : EReal) ≤ φ y := by sorry
