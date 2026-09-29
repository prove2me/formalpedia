-- Prove2me | Theorems.Thm_HolomorphicOn_riemannZeta
-- name    : HolomorphicOn_riemannZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:21:20.626835+00:00
-- url     : https://prove2.me/theorems/3cb5dcbf-084e-4f96-8a91-433cbf712076
-- title:
--   The Riemann zeta function is holomorphic away from $s = 1$
-- statement:
--   The Riemann zeta function $\zeta$ is holomorphic on the complement of its unique pole:
--   $$\zeta \in \mathcal{O}\bigl(\{s \in \mathbb{C} : s \neq 1\}\bigr),$$
--   i.e. $\zeta$ is complex-differentiable at every point of the open set $\mathbb{C} \setminus \{1\}$.
--
--   This packages the analytic continuation of $\zeta$ (initially defined by the Dirichlet series $\sum_{n\ge1} n^{-s}$ for $\operatorname{Re} s > 1$) into the `HolomorphicOn` predicate on the punctured plane, the form in which it can be fed directly to the rectangle contour-integration machinery.
--
--   In the PNT+ project this is the basic analyticity input for all contour-shifting arguments involving $\zeta$ and $\zeta'/\zeta$: away from $s = 1$ (and off the zeros, for the logarithmic derivative) the integrands in the Perron/Mellin representation of the smoothed Chebyshev function are holomorphic, enabling the deformation of contours into the zero-free region.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1092-L1096

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by sorry
