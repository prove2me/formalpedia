-- Prove2me | Theorems.Thm_HasDerivAtZeta0
-- name    : HasDerivAtZeta0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:24:55.330172+00:00
-- url     : https://prove2.me/theorems/31c46bf5-fcd6-4ad6-bd6c-48b09ba79827
-- title:
--   Differentiability of the truncated zeta function $\zeta_0$ with explicit derivative $\zeta_0'$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$ and $s \neq 1$. The truncated (Euler-Maclaurin) zeta representation
--   $$\zeta_0(N, s) = \sum_{n=1}^{N} n^{-s} - \frac{N^{1-s}}{1-s} - \frac{N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x \rfloor + \tfrac{1}{2} - x}{x^{s+1}}\, dx$$
--   is complex-differentiable at $s$, with derivative given by the explicit term-by-term expression $\zeta_0'(N, s)$:
--   $$\frac{d}{ds}\,\zeta_0(N, s) = \zeta_0'(N, s),$$
--   where $\zeta_0'(N,\cdot)$ is the formula obtained by differentiating each summand and differentiating under the integral sign.
--
--   The content of the theorem is analytic: it justifies differentiation of the finite Dirichlet polynomial, of the boundary terms $-N^{1-s}/(1-s)$ and $-N^{-s}/2$, and — the delicate part — differentiation under the integral sign in the sawtooth remainder integral, all on the region $\operatorname{Re} s > 0$, $s \neq 1$.
--
--   Because every term of $\zeta_0'$ is explicit, this theorem is the engine behind the effective upper bounds for $|\zeta'(s)|$ near the $1$-line in the PNT+ project: one bounds each explicit term of $\zeta_0'$, then transports the bound to $\zeta'$ via the identity $\frac{d}{ds}\zeta_0(N,s) = \zeta'(s)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1070-L1085

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

theorem HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by sorry
