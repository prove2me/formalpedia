-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_real_legendre_408915f
-- name    : FunctionalInequalities.Analysis.lipschitzWith_real_legendre_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:29.194373+00:00
-- url     : https://prove2.me/theorems/88b11f23-ae80-4131-9826-e6c0ec40509e
-- title:
--   Lipschitz Representative of a Finite Legendre Transform
-- statement:
--   This shows that bounded effective-domain slopes yield a Lipschitz real representative of the Legendre transform.
--
--   Let $E$ be a real inner-product space, let $q:E\to\overline{\mathbb R}$, let $L\in[0,\infty)$, and let $\psi:E\to\mathbb R$. Assume:
--
--   1. $q(y)\neq-\infty$ for every $y$;
--   2. whenever $q(y)\neq+\infty$, one has $y\in\overline B(0,L)$;
--   3. $\operatorname{Leg}(q)(x)=\psi(x)$ as an extended-real equality for every $x$.
--
--   Then `ψ` is $L$-Lipschitz, expressed by `LipschitzWith L ψ`.
--
--   Only finite values of $q$ are converted using `toReal`; the supremum itself remains an extended-real supremum.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L175-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.lipschitzWith_real_legendre`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.lipschitzWith_real_legendre_408915f
    (q : E → EReal) (L : NNReal) (ψ : E → ℝ)
    (hbot : ∀ y, q y ≠ ⊥)
    (hdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    LipschitzWith L ψ := by sorry
