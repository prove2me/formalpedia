-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasDerivAt_legendre_add_smul_of_dualDifferentiable_408915f
-- name    : FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:30.01699+00:00
-- url     : https://prove2.me/theorems/95202841-2d5c-4270-a444-dcdaac4f7212
-- title:
--   Pointwise Legendre First Variation
-- statement:
--   This is a pointwise first-variation formula for the Legendre transform under a bounded continuous perturbation.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\phi:E\to\overline{\mathbb{R}}$ be a proper lower-semicontinuous potential. Let $y$ lie in the interior of the finite domain of $\phi^*$, and assume $q\mapsto(\phi^*(q)).toReal$ is differentiable at $y$. Let $b:E\to\mathbb{R}$ be continuous and assume $|b|$ is bounded above. Then the map
--
--   $$
--   t\longmapsto\bigl(\phi+t b\bigr)^*(y).toReal
--   $$
--
--   has derivative at $0$ equal to
--
--   $$
--   -b\bigl(\nabla(\phi^*).toReal(y)\bigr).
--   $$
--
--   Here $(\phi+t b)(z)$ denotes $\phi(z)+(t b(z):\overline{\mathbb{R}})$. No differentiability or global finiteness of $\phi$ is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L242-L436 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, declaration `FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
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
section Variation
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

theorem FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q => (legendre φ q).toReal) y)
    (b : E → ℝ) (hb : Continuous b)
    (hbounded : BddAbove (Set.range fun z : E => |b z|)) :
    HasDerivAt
      (fun t : ℝ =>
        (legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y).toReal)
      (-b (gradient (fun q => (legendre φ q).toReal) y)) 0 := by sorry
