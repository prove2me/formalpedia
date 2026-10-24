-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_comp_affineEquiv_symm_408915f
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:35.148693+00:00
-- url     : https://prove2.me/theorems/76d6e475-83ef-4a14-b77f-797b96ca31e1
-- title:
--   Volume Scaling of Transported Subgradient Images
-- statement:
--   This gives the volume-scaling version of affine transport for subgradient images.
--
--   Let $E$ be a finite-dimensional real inner-product space with measurable and Borel structures, let $u:E\to\mathbb R$, let $e:E\simeq_A E$, and let $G\subseteq E$. Writing $T=e.linear$, one has
--
--   $$
--   \operatorname{vol}\big(\operatorname{subgradientImage}(u\circ e^{-1},e(G))\big)
--   =\operatorname{ofReal}\!\left(|\det T|^{-1}\right)\operatorname{vol}\big(\operatorname{subgradientImage}(u,G)\big).
--   $$
--
--   The volume values lie in $[0,\infty]$ (`ENNReal`), while the determinant factor is embedded with `ofReal`. The declaration is `volume_subgradientImage_comp_affineEquiv_symm`; no finiteness of either measured set is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1858-L1939 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_408915f [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (subgradientImage u G) := by sorry
