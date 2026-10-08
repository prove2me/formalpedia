-- Prove2me | Theorems.Thm_OAI_GammaFPP_gamma_differentiability
-- name    : OAI.GammaFPP.gamma_differentiability
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:41.978378+00:00
-- url     : https://prove2.me/theorems/b7de25f2-b54a-4efc-8ab8-477206a18f05
-- statement:
--   The theorem states that for all real shape and rate parameters with shape > 0 and rate > 0, and for every probability space (Ω, P) with Ω in Type and a family τ of random edge weights indexed by the edges of the square lattice ℤ² (each edge being a vertex together with a Boolean indicating its horizontal or vertical direction), if the τ(e) are measurable, mutually independent and each has the Gamma distribution with that shape and rate as its law, then there exists a function μ from the Euclidean plane ℝ² to ℝ with four properties. First, μ is a norm in the sense that it is nonnegative, vanishes only at 0, satisfies the triangle inequality, and is absolutely homogeneous, μ(av) = |a|μ(v). Second, μ is the almost-sure time constant: for every vector v, with probability one, the first-passage time (the infimum of summed edge weights over nearest-neighbour paths) from the origin to the lattice point obtained by taking coordinatewise floors of tv, divided by t, converges to μ(v) as t → ∞. Third, μ is Fréchet differentiable at every nonzero point. Fourth, every point v on the boundary of the unit ball {z : μ(z) ≤ 1} has a regular C¹ chart: an open neighbourhood U of v, a C¹ curve γ from ℝ into the boundary with nowhere-vanishing derivative and values in the boundary intersected with U, and a continuous map θ on U with θ(γ(t)) = t and γ(θ(z)) = z for every boundary point z in U. No shape theorem, norm, or absence-of-corners hypothesis is assumed; they are all conclusions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GammaPassage.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GammaPassage.lean; bytes 3897..3973
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Basic
import Definitions.Def_GammaPassage

namespace OAI

namespace GammaFPP

open Set MeasureTheory ProbabilityTheory PlanarFPP

theorem gamma_differentiability : GammaDifferentiabilityTarget := by
  sorry

end GammaFPP
end OAI
