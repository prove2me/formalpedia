-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convexOn_quadraticAt_408915f
-- name    : FunctionalInequalities.Analysis.convexOn_quadraticAt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:43.006425+00:00
-- url     : https://prove2.me/theorems/8ed1797b-f732-43ee-a82a-0f010fd16348
-- title:
--   Convexity of Positive Semidefinite Quadratics
-- statement:
--   This proves convexity of a quadratic with positive semidefinite matrix.
--
--   Let $n\in\mathbb N$, let $A$ be a real $n\times n$ matrix indexed by `Fin n`, and assume $A$ is positive semidefinite. For any $x_0,b\in\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}n)$ and $c\in\mathbb R$, the function `quadraticAt A x₀ b c` is convex on the whole space:
--   $$\operatorname{ConvexOn}\bigl(\mathbb R,\operatorname{univ},\operatorname{quadraticAt}(A,x_0,b,c)\bigr).$$
--
--   This is a finite-dimensional algebraic lemma for constructing convex quadratic potentials. No positivity or dimension restriction on $n$ is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1584-L1601 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.convexOn_quadraticAt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.convexOn_quadraticAt_408915f {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (quadraticAt A x₀ b c) := by sorry
