-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ConvexOn_ae_differentiableAt_of_isOpen_408915f
-- name    : FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:38.68957+00:00
-- url     : https://prove2.me/theorems/102ce8eb-0734-4e82-a9f0-b8a56fdddc7e
-- title:
--   Almost-Everywhere Differentiability of Convex Functions
-- statement:
--   This statement gives almost-everywhere differentiability of a convex function on an open set.
--
--   Let $E$ be a finite-dimensional real normed space with its Borel measurable structure, let $\mu$ be an additive Haar measure on $E$, and let $U\subseteq E$ be open. If $f:E\to\mathbb R$ is convex on $U$, then
--
--   $$
--   \text{for }\mu\text{-almost every }x,\quad x\in U\implies f\text{ is differentiable at }x.
--   $$
--
--   Equivalently, the exceptional set of points in $U$ where differentiability fails is $\mu$-null. This technical result supports almost-everywhere arguments involving subgradients of convex functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L567-L618 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
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
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LT14A0ConvexAeDifferentiable
open MeasureTheory Set

theorem FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_408915f {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by sorry
