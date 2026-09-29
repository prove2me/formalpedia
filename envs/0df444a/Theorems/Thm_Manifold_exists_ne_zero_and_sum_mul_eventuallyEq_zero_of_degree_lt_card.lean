-- Prove2me | Theorems.Thm_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
-- name    : Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/989e8019-0d75-54d8-9bdb-fd29d5cccc64
-- title:
--   Chartwise bound dim L(D)≤ deg D+1 on a compact Riemann surface
-- statement:
--   Let $M$ be a topological space equipped with a charted structure over $\mathbb{C}$ which is an analytic ($\omega$-smooth) manifold with respect to the model $\mathcal{I}(\mathbb{C},\mathbb{C})$, and assume $M$ is compact and connected; thus $M$ is a compact connected Riemann surface, possibly presented without further structure. Let $D : M \to_{f} \mathbb{N}$ be a finitely supported function on $M$ (an effective divisor), let $\iota$ be a finite type, and let $\psi : \iota \to M \to \mathbb{C}$ be a family of complex-valued functions. Assume that for every $i$ and every $x \in M$ the reading $z \mapsto \psi_i((\mathrm{extChartAt}\ x)^{-1}(z))$ of $\psi_i$ in the extended chart at $x$ is meromorphic at the centre $\mathrm{extChartAt}\ x\ (x)$, and that its meromorphic order there is at least $-D(x)$ as an element of $\mathbb{Z} \cup \{\infty\}$. Assume further that $\left(\sum_{x} D(x)\right) + 1 < \#\iota$, the sum being $D$'s total mass. Then there is a nonzero vector $c : \iota \to \mathbb{C}$ such that for every $x \in M$ the chart reading $z \mapsto \sum_i c_i\,\psi_i((\mathrm{extChartAt}\ x)^{-1}(z))$ agrees with $0$ on a punctured neighbourhood of $\mathrm{extChartAt}\ x\ (x)$, i.e. eventually along the filter $\mathcal{N}[\ne]$ at that point. The vanishing is asserted only off the chart centres, so nothing is claimed about the values $\psi_i(x)$ themselves.
--
--   This is the elementary upper bound $\dim L(D) \le \deg D + 1$ for the space of meromorphic functions on a compact Riemann surface with poles bounded by an effective divisor $D$, stated as a linear-dependence statement for a family of functions given chartwise. It is cited in the construction of evaluation maps for algebraic curves, via [`AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt`](thm.html#AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt), and rests on the fact that a function whose chart readings are meromorphic of nonnegative order at every point is locally constant off the chart centres ([`Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg`](thm.html#Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

theorem Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0 := by sorry
