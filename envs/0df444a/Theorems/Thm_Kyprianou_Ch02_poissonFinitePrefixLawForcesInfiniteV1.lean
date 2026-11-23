-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonFinitePrefixLawForcesInfiniteV1
-- name    : Kyprianou.Ch02.poissonFinitePrefixLawForcesInfiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:15:35.611777+00:00
-- url     : https://prove2.me/theorems/6972ecdf-46ff-4a25-9be8-a0dc080a30ea
-- title:
--   Diverging Poisson partial laws force an infinite dominating count a.e.
-- statement:
--   On a probability space, suppose Nat-valued partial counts each have a Poisson law with intensity tending to infinity and they are pointwise dominated by an extended nonnegative random variable f. Every finite upper bound on f yields an event whose probability is bounded by the Poisson lower tail at every partial stage, and these tails tend to zero. By countable union and the existence of natural upper bounds for finite ENNReal values, f is infinite almost surely.
-- source:
--   Source-faithful Kyprianou Chapter 2 Theorem 2.4 decomposition, via exact Poisson partial distribution and finite-tail lemma.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem poissonFinitePrefixLawForcesInfiniteV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ENNReal)
    (C : ℕ → Ω → ℕ) (rate : ℕ → NNReal)
    (hC : ∀ n, Measurable (C n))
    (hlaw : ∀ n, P.map (C n) = ProbabilityTheory.poissonMeasure (rate n))
    (hdom : ∀ n ω, (C n ω : ENNReal) ≤ f ω)
    (hrate : Tendsto rate atTop atTop) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by sorry
end Kyprianou.Ch02
