-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_proposition_4_3
-- name    : InvMarketMaking.LOB.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:40.744732+00:00
-- url     : https://prove2.me/theorems/4bc29ec3-ee82-42af-9aaa-e8d679f4c2e8
-- title:
--   Proposition 4.3 — the uniform $1/N$-grid loses at most $2/N$ of $J^*$
-- statement:
--   Let $\mathcal V$ be a probability law of valuation pairs, with seller c.d.f. $F$ and buyer survival function $S$, and $J(b,a)=(a-b)\min\{F(b),S(a)\}$. Let $N\ge1$ and $\mathcal G_N=\{n/N:n=0,\dots,N\}$. Then
--   $$
--   \max_{(b,a)\in\mathcal G_N\times\mathcal G_N}J(b,a)\;\ge\;\sup_{(b,a)\in[0,1]^2}J(b,a)-\frac2N .
--   $$
--   The surrogate objective is thus nearly attained on a coarse grid even when $F$ and $S$ are discontinuous, which lets the learning algorithms work with finitely many prices.
--
--   Differences from the source:
--   - generalization: F, S of a law on [0,1]² with P(V^buy = 1) = P(V^sell = 0) = 0 → any probability law V on ℝ²; reason: the result needs only that F is nondecreasing, S nonincreasing and both [0,1]-valued; the paper's laws are instances
--   - encoding: max over G_N² of J ≥ sup J − 2/N → some grid pair (b, a) has J(b, a) ≥ J* − 2/N; reason: the grid is finite and nonempty, so the maximum is attained
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 4.3, p. 19

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_grid

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Proposition 4.3** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential
Market Making Under Inventory Constraints, arXiv:2610.24562v1, p. 19). For `N ≥ 1` and the uniform
grid `𝒢_N = {n/N : n = 0, …, N}`, `max_{(b,a) ∈ 𝒢_N²} J(b, a) ≥ sup_{(b,a) ∈ [0,1]²} J(b, a) − 2/N`.

**Formalization Note** The maximum over the finite grid is stated as the existence of a grid pair
attaining the bound. `V` is any probability law on `ℝ²`: the proof uses only that `F` is
nondecreasing, `S` nonincreasing and both `[0,1]`-valued, so the standing assumptions of Sec. 3 are
not needed. -/
theorem proposition_4_3 (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (N : ℕ) (hN : 0 < N) :
    ∃ b ∈ grid N, ∃ a ∈ grid N, Jstar V - 2 / N ≤ J V b a := by sorry

end InvMarketMaking.LOB
