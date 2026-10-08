-- Prove2me | Theorems.Thm_OAI_PlanarFPP_manuscriptMain
-- name    : OAI.PlanarFPP.manuscriptMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:04.195189+00:00
-- url     : https://prove2.me/theorems/64da51ab-4dde-4e1a-8fac-f879b5802cc4
-- statement:
--   The theorem states that, for any probability space (Ω, P) carrying an edge-weight family τ indexed by the edges of the nearest-neighbour lattice ℤ², where each vertex p has an east edge (p,false) and a north edge (p,true), such that the τ(e) are measurable, mutually independent, and each has the exponential distribution with rate 1 (the ExponentialEnvironment hypothesis), there exists a function μ on the plane ℝ² with the following properties. First, μ is a norm: nonnegative, zero only at the origin, subadditive, and satisfying μ(av)=|a|μ(v) for all real a. Second, μ is the time constant: for every v in ℝ², almost surely the first-passage time from (0,0) to the lattice point (⌊tv₀⌋,⌊tv₁⌋), defined as the infimum of path costs over nearest-neighbour step sequences (east, west, north, south) that sum the edge weights along the path, divided by t, converges to μ(v) as t→∞. Third, μ is Fréchet differentiable at every nonzero point. Fourth, at every point v with μ(v)=1 there is exactly one linear functional ℓ with ℓ(v)=1 and ℓ(w)≤μ(w) for all w. Fifth, the unit sphere of μ is a C¹ curve in the sense that near each point v with μ(v)=1 there is an open neighbourhood U and a C¹ function g on U whose zero set in U is exactly the set where μ=1, with g having a nonzero Fréchet derivative at each of those zeros. Sixth, for each boundary point v of the unit ball {μ≤1}, there is a unique line L that is the level set {z : g(z)=g(v)} of some nonzero continuous linear functional g that attains its maximum over the unit ball at v, so each boundary point has a unique supporting line. Seventh, every boundary point v of the unit ball has a C¹ curve chart: an open neighbourhood U of v and a C¹ map γ:ℝ→ℝ² with nowhere vanishing derivative, together with a function θ continuous on U, such that γ takes values in the boundary within U, θ(γ(t))=t for all t, and γ(θ(z))=z for each boundary point z in U.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarFirstPassage.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarFirstPassage.lean; bytes 3261..3855
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Definitions.Def_PlanarFirstPassage

namespace OAI

namespace PlanarFPP

open Set MeasureTheory ProbabilityTheory Filter

open scoped Topology

theorem manuscriptMain (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (henv : ExponentialEnvironment P τ) :
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, ∃! L : Set Plane,
        ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧ (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v}) ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, HasC1CurveChart (frontier {z | μ z ≤ 1}) v) := by
  sorry

end PlanarFPP
end OAI
