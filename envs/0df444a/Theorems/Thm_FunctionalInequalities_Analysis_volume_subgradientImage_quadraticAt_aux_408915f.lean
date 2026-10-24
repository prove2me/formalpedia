-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_quadraticAt_aux_408915f
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:48.335087+00:00
-- url     : https://prove2.me/theorems/7a3997d1-278d-46b0-8bd4-a0cf40b24f1f
-- title:
--   Volume Formula for Quadratic Subgradient Images
-- statement:
--   This is an auxiliary volume identity for quadratic subgradient images.
--
--   Let $A$ be a positive-definite real $n\times n$ matrix, let $x_0,b\in\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$, let $c\in\mathbb R$, and let $G$ be any subset of that Euclidean space. Then the Lebesgue volume of the subgradient image of $G$ under `quadraticAt` is
--   $$\operatorname{vol}\bigl(\operatorname{subgradientImage}(\operatorname{quadraticAt}(A,x_0,b,c),G)\bigr)
--   =\operatorname{ofReal}(\det A)\,\operatorname{vol}(G).$$
--
--   The determinant factor is represented as an `ENNReal` value through `ENNReal.ofReal`. This identity is a reusable change-of-variables formula for the affine gradient map of a positive-definite quadratic.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1603-L1660 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `_private.FunctionalInequalities.Analysis.Convex.Alexandrov.0.FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_408915f
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {G : Set (EuclideanSpace ℝ (Fin n))} :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by sorry
