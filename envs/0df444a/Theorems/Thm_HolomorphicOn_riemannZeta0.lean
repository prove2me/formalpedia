-- Prove2me | Theorems.Thm_HolomorphicOn_riemannZeta0
-- name    : HolomorphicOn_riemannZeta0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:25:24.336003+00:00
-- url     : https://prove2.me/theorems/83b7abaf-7382-4e15-a07e-1ca2e034a9fd
-- title:
--   The truncated zeta representation $\zeta_0(N,\cdot)$ is holomorphic on $\{\operatorname{Re} s > 0\} \setminus \{1\}$
-- statement:
--   Let $N$ be a positive natural number. The truncated (Euler-Maclaurin) zeta function
--   $$\zeta_0(N, s) = \sum_{n=1}^{N} n^{-s} - \frac{N^{1-s}}{1-s} - \frac{N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x \rfloor + \tfrac{1}{2} - x}{x^{s+1}}\, dx$$
--   is holomorphic on the set
--   $$\{s \in \mathbb{C} : s \neq 1 \text{ and } \operatorname{Re} s > 0\}.$$
--
--   Each ingredient is analytic there: the Dirichlet polynomial and the boundary terms are elementary (the factor $1/(1-s)$ excludes $s=1$), and the sawtooth remainder integral converges locally uniformly for $\operatorname{Re} s > 0$, hence defines a holomorphic function.
--
--   The representation $\zeta_0$ extends the zeta function into the critical strip with completely explicit terms; its holomorphy is what allows the PNT+ project to differentiate it, compare it with $\zeta$ and $\zeta'$, and derive the effective upper bounds for $|\zeta(s)|$ and $|\zeta'(s)|$ near the $1$-line that underlie the zero-free region and the error term in the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1087-L1089

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

theorem HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} := by sorry
