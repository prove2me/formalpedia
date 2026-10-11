-- Prove2me | Theorems.Thm_KPZBallistic_penrose_prop_2_1
-- name    : KPZBallistic.penrose_prop_2_1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:29:42.510734+00:00
-- url     : https://prove2.me/theorems/42dd9fe6-9a3b-447c-8e3c-a45865ff17d5
-- title:
--   Penrose Prop. 2.1: a.s. finiteness and $E[\xi_t(0)^k]=O(t^k)$
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, let $\xi_t(0)$ be the (last-arrival) height and $\eta_t(0)=\max\{\xi_t(0)+1,\xi_t(-1),\xi_t(1)\}$ the next-arrival height of column $0$ at time $t$.
--
--   1. For every $t\in(0,\infty)$, $\xi_t(0)$ and $\eta_t(0)$ are almost surely finite.
--   2. For every $k\in\mathbb N$, as $t\to\infty$,
--   $$
--   E[\xi_t(0)^k]=O(t^k),\qquad E[\eta_t(0)^k]=O(t^k).
--   $$
--
--   Part 1 says the infinite-substrate process does not explode; part 2 gives the moment bounds used throughout the analysis of the model.
--
--   **Formalization Note** The moments are lower Lebesgue integrals of the $\mathbb N\cup\{\infty\}$-valued heights, taken in $[0,\infty]$.
-- source:
--   M. D. Penrose, Growth and roughness of the interface for ballistic deposition, J. Stat. Phys. 131 (2008), https://arxiv.org/abs/math/0608540, Section 2, Proposition 2.1, p. 4 (case d = 1, nearest-neighbour model)

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem penrose_prop_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    (∀ t > 0, (∀ᵐ ω ∂P, bdHeight τ t 0 ω < ⊤) ∧ (∀ᵐ ω ∂P, bdNextHeight τ t 0 ω < ⊤)) ∧
    ∀ k : ℕ, ∃ C T : ℝ, ∀ t ≥ T,
      (∫⁻ ω, ((bdHeight τ t 0 ω : ℕ∞) : ENNReal) ^ k ∂P) ≤ ENNReal.ofReal (C * t ^ k) ∧
      (∫⁻ ω, ((bdNextHeight τ t 0 ω : ℕ∞) : ENNReal) ^ k ∂P) ≤ ENNReal.ofReal (C * t ^ k) := by sorry

end KPZBallistic
