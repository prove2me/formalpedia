-- Prove2me | Theorems.Thm_MediumPNT
-- name    : MediumPNT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:08:38.138986+00:00
-- url     : https://prove2.me/theorems/7cfa31c8-4063-4b52-81fc-8b2f2a59495e
-- title:
--   Prime Number Theorem with error term $\psi(x)=x+O\bigl(x\exp(-c(\log x)^{1/10})\bigr)$
-- statement:
--   There exists a constant $c>0$ such that the Chebyshev function $\psi(x)=\sum_{n\le x}\Lambda(n)$ (the summatory function of the von Mangoldt function) satisfies, as $x\to\infty$,
--
--   $$\psi(x)-x \;=\; O\!\left(x\,\exp\!\bigl(-c\,(\log x)^{1/10}\bigr)\right).$$
--
--   Equivalently, $\psi(x)\sim x$ with an error term that saves a factor $\exp(c(\log x)^{1/10})$ — stronger than any power of $\log x$, though weaker than the classical de la Vallée-Poussin error $\exp(-c\sqrt{\log x})$. This "medium strength" form is what comes out of the classical zero-free region combined with the mollified-contour method: the smoothed Chebyshev function is written as a vertical contour integral of $-\frac{\zeta'}{\zeta}(s)\,\mathcal{M}(\widetilde{1_\varepsilon})(s)\,X^s$, the contour is pulled into a zero-free region of width $A/(\log T)^9$, the residue at $s=1$ produces the main term $X$, and optimizing the smoothing width $\varepsilon$ and the height $T$ against each other yields the exponent $1/10$.
--
--   This is the capstone theorem of the `MediumPNT` module of the PrimeNumberTheoremAnd project, and by the standard partial-summation equivalences it yields the corresponding error term for $\pi(x)$ and for $\theta(x)$. It sits between the elementary/Tauberian PNT (no explicit error) and the strong form with $\exp(-c\sqrt{\log x})$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L3144-L3715

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED

open Filter Topology
set_option maxHeartbeats 400000

theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by sorry
