-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_subset_of_le_408915f
-- name    : FunctionalInequalities.Analysis.subgradientImage_subset_of_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:36.344971+00:00
-- url     : https://prove2.me/theorems/9f87aac3-4538-46d6-9379-190a39eb575d
-- title:
--   Monotonicity of Subgradient Images
-- statement:
--   This formalizes the comparison principle stated as Lemma 1.4.1 of Gutiérrez, *The Monge–Ampère equation*.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, and let $u,v:E\to\mathbb R$ be convex on all of $E$. Let $\Omega\subseteq E$ be open and bounded. Assume:
--
--   1. $u(x)\le v(x)$ for every $x\in\Omega$;
--   2. $u(x)=v(x)$ for every $x\in\partial\Omega$.
--
--   Writing `subgradientImage` for the set of vectors that are subgradients at points of a set, the conclusion is
--   $$\operatorname{subgradientImage}(v,\Omega)\subseteq \operatorname{subgradientImage}(u,\Omega).$$
--
--   This is a finite-dimensional comparison result for convex subgradient images and is reusable in Alexandrov- and Monge–Ampère-type arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L989-L1045 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.subgradientImage_subset_of_le`; the repository is private at upload time).

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
section LT12ASubgradientImageMonotone
open Set
open scoped RealInnerProductSpace
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_subset_of_le_408915f
    [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImage v Ω ⊆ subgradientImage u Ω := by sorry
