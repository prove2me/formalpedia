-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_real_convexOn_legendre_408915f
-- name    : FunctionalInequalities.Analysis.real_convexOn_legendre_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:29.052616+00:00
-- url     : https://prove2.me/theorems/d7403aea-3697-486e-a293-003d7f2730be
-- title:
--   Convexity of a Real Legendre Representative
-- statement:
--   This transfers convexity of the extended-real Legendre epigraph to a real representative.
--
--   Let $E$ be a real inner-product space, let $q:E\to\overline{\mathbb R}$, and let $\psi:E\to\mathbb R$. Assume that for every $x\in E$,
--
--   $$
--   \operatorname{Leg}(q)(x)=\psi(x)
--   $$
--
--   where the right-hand side is coerced to `EReal`. Then $\psi$ is convex on all of $E$:
--
--   $$
--   \psi(a x+b y)\leq a\psi(x)+b\psi(y)
--   $$
--
--   whenever $a,b\geq0$ and $a+b=1$. No finite-dimensional, measurability, or bounded-domain hypothesis is required.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L155-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.real_convexOn_legendre`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.real_convexOn_legendre_408915f
    (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    ConvexOn ℝ (univ : Set E) ψ := by sorry
