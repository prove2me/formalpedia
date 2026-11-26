-- Prove2me | Theorems.Thm_NullConeCut_finite_dimensional_of_closed_sewing
-- name    : NullConeCut.finite_dimensional_of_closed_sewing
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:54:32.79215+00:00
-- url     : https://prove2.me/theorems/05ba10eb-241a-575f-b92b-89c7b1b7ba15
-- title:
--   Finite dimensionality from a positive closed-cut limit (Eq. 5.38)
-- statement:
--   Let $E$ be a complex vector space. Let $P$ range over finite subsets of a nonempty set of complete cycles, ordered by inclusion. Write $w(P)$ for the weight, $m(P)$ for the mean, and $\delta$ for a real threshold. Assume $w(P)\ge 0$ on every nonempty cutoff. Suppose that if $E$ is infinite-dimensional, then $m(P)\le\delta/2$ for every nonempty $P$. If the signed amplitudes $w(P)(m(P)-\delta/2)$ converge to a strictly positive number $Z$, then $E$ is finite-dimensional.
--
--   The convergence to the uncut amplitude is an explicit hypothesis of this conditional form of the argument following Eq. (5.38).
-- source:
--   Venkatesa Chandrasekaran, An algebraic quantization of gravity from the null cone, arXiv:2611.34924v1, §5.2, Eq. (5.38) and the finite-dimensionality inference immediately following it. https://arxiv.org/html/2611.34924v1#S5.E38

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Finset

open Filter
open scoped Topology

namespace NullConeCut
theorem finite_dimensional_of_closed_sewing {E : Type*} [AddCommGroup E] [Module ℂ E]
    {Cycle : Type*} [Nonempty Cycle] (weight mean : Finset Cycle → ℝ) (δ Z : ℝ)
    (uncut_pos : 0 < Z)
    (weights : ∀ P, P.Nonempty → 0 ≤ weight P)
    (cut_estimate : ¬ FiniteDimensional ℂ E → ∀ P, P.Nonempty → mean P ≤ δ / 2)
    (sewing : Tendsto (fun P => weight P * (mean P - δ / 2)) atTop (𝓝 Z)) :
    FiniteDimensional ℂ E := by sorry
end NullConeCut
