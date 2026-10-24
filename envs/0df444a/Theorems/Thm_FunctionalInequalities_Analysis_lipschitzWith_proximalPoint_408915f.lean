-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_proximalPoint_408915f
-- name    : FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:06.699499+00:00
-- url     : https://prove2.me/theorems/945fe6f8-b1c5-4364-9e15-82a446b692f0
-- title:
--   The Proximal Map Is One-Lipschitz
-- statement:
--   This formalizes the nonexpansiveness property of the proximal map.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $f:E\to\mathbb R$ be convex on all of $E$. For the Lean definition `proximalPoint f`, the map is $1$-Lipschitz:
--
--   $$\|\operatorname{prox}_f(z)-\operatorname{prox}_f(w)\|\le \|z-w\|\qquad(z,w\in E).$$
--
--   Equivalently, `proximalPoint f` is `LipschitzWith 1`. This declaration supplies a global continuity estimate used by later almost-everywhere differentiability arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L161-L178 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.lipschitzWith_proximalPoint`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
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
section LT12D2ProximalPoint
open Set
open scoped RealInnerProductSpace
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
section FiniteDimensional
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_408915f {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    LipschitzWith 1 (proximalPoint f) := by sorry
