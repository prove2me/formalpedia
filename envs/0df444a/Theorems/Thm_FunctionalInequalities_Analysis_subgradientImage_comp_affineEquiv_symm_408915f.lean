-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_comp_affineEquiv_symm_408915f
-- name    : FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:47.976787+00:00
-- url     : https://prove2.me/theorems/18a6973c-6167-4d0e-bc77-4c6b930fe9a5
-- title:
--   Affine Transport of Subgradient Images
-- statement:
--   This establishes the affine transport law for subgradient images.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$, let $e:E\simeq_A E$ be an affine equivalence, and let $G\subseteq E$. If $T=e.linear$ is the linear part of $e$, then
--
--   $$
--   \operatorname{subgradientImage}(u\circ e^{-1},e(G))
--   =
--   \operatorname{adj}(T^{-1})\big(\operatorname{subgradientImage}(u,G)\big).
--   $$
--
--   The image on the right is the set image under the adjoint of the inverse linear part. The declaration is `subgradientImage_comp_affineEquiv_symm`; it is an exact set equality and does not involve volume or determinant factors.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1771-L1856 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm`; the repository is private at upload time).

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
section LT11E1AffineTransportSubgradientimage
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_408915f (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G := by sorry
