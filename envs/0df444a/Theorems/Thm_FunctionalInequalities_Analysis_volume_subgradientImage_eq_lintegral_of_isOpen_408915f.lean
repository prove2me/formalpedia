-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_eq_lintegral_of_isOpen_408915f
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:08.110748+00:00
-- url     : https://prove2.me/theorems/3fe1e844-44bc-4402-87a7-f059df3458d9
-- title:
--   Open-Set Alexandrov Volume Formula
-- statement:
--   This is the Alexandrov volume identity for open sets in the moment-map setting.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume
--   $$\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1.$$
--   Let $K\subseteq E$ be closed and convex, let $V:E\to\mathbb R$ be measurable, and suppose the push-forward of the tilted volume measure by $\nabla u$ equals the measure with density
--   $$1_K(p)\,\operatorname{ofReal}(e^{-V(p)}).$$
--   Then every open set $G\subseteq E$ satisfies
--   $$\operatorname{vol}(\partial u(G))
--   =\int_G \operatorname{ofReal}\!\left(e^{-u(x)+V(\nabla u(x))}\right)\,d\operatorname{vol}(x).$$
--
--   This formula is a central measure identity for the moment potential and is used to derive local Monge–Ampère bounds.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2191-L2329 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen`; the repository is private at upload time).

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
section LT14DAlexandrovIdentityOpen
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
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {G : Set E} (hG : IsOpen G) :
    (volume : Measure E) (subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E) := by sorry
