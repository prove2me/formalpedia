-- Prove2me | Theorems.Thm_HasDerivAt_neg_cpow_over2
-- name    : HasDerivAt_neg_cpow_over2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:22:20.144052+00:00
-- url     : https://prove2.me/theorems/b6cc4238-3521-4aee-ba24-52d8d15009e6
-- title:
--   Derivative of $z \mapsto -N^{-z}/2$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ be arbitrary. Then the function $x \mapsto -N^{-x}/2$ is complex-differentiable at $s$, with
--   $$\frac{d}{dx}\left(-\frac{N^{-x}}{2}\right)\bigg|_{x=s} = \frac{-\bigl((-\log N)\, N^{-s}\bigr)}{2} = \frac{(\log N)\, N^{-s}}{2},$$
--   where $\log N$ is the real natural logarithm of $N$.
--
--   This is the chain rule applied to the entire function $x \mapsto N^{-x} = e^{-x \log N}$; positivity of $N$ ensures the complex power is given by the exponential formula with no branch issues.
--
--   The lemma supplies the derivative of the $-N^{-s}/2$ boundary term in the truncated Euler-Maclaurin zeta representation $\zeta_0$, one of the explicit pieces assembled into $\zeta_0'$ for the PNT+ project's bounds on $\zeta'$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1049-L1052

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

theorem HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by sorry
