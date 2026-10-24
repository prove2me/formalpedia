-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_quadraticAt_subgradient_iff_408915f
-- name    : FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:44.397165+00:00
-- url     : https://prove2.me/theorems/392b734d-17ed-4e0c-a959-421408454320
-- title:
--   Subgradient Characterization of a Positive Semidefinite Quadratic
-- statement:
--   This is a technical characterization of subgradients of the quadratic function `quadraticAt`.
--
--   Let $n\in\mathbb N$, let $A$ be a positive semidefinite real matrix indexed by $\operatorname{Fin}(n)$, and let $x_0,b,x,p\in\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. For $c\in\mathbb R$, the following are equivalent:
--
--   1. for every $y$,
--   $$q(x)+\langle p,y-x\rangle\le q(y),$$
--   where $q(z)=\operatorname{quadraticAt}(A,x_0,b,c,z)$;
--   2. $p=b+A(x-x_0)$, with $A$ interpreted through `Matrix.toEuclideanLin`.
--
--   Thus,
--   $$\bigl(\forall y,\ q(x)+\langle p,y-x\rangle\le q(y)\bigr)\iff p=b+A(x-x_0).$$
--
--   The lemma gives the exact affine formula for every subgradient of this positive semidefinite quadratic, including the degenerate case.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1470-L1537 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `_private.FunctionalInequalities.Analysis.Convex.Alexandrov.0.FunctionalInequalities.Analysis.quadraticAt_subgradient_iff`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_408915f {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    (∀ y, quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ quadraticAt A x₀ b c y) ↔
      p = b + Matrix.toEuclideanLin A (x - x₀) := by sorry
