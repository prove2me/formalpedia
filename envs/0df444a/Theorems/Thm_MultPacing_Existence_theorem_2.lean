-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_2
-- name    : MultPacing.Existence.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:00.443352+00:00
-- url     : https://prove2.me/theorems/8fb455df-d545-4c13-8bd5-e1befe5a470c
-- title:
--   Theorem 2, p. 11 — for H > M/ϵ the (ϵ,H)-smoothed pacing game has a pure-strategy Nash equilibrium
-- statement:
--   Consider a pacing game with valuations $v_{ij}\ge0$ and budgets $B_i>0$, a smoothing parameter $\epsilon>0$ and the $(\epsilon,H)$-smoothed pacing game, in which a strategy of buyer $i$ is a multiplier $\alpha_i\in[0,1]$. Let $M$ be an upper bound on the sum of every buyer's valuations including the artificial good, that is
--   $$
--   \sum_j v_{ij}+2\epsilon\le M\quad\text{for every buyer } i .
--   $$
--   If $H>M/\epsilon$, the smoothed game has a pure-strategy Nash equilibrium: a profile $\alpha\in[0,1]^N$ such that $u_i(a,\alpha_{-i})\le u_i(\alpha)$ for every buyer $i$ and every $a\in[0,1]$.
--
--   The equilibria of the smoothed games are the approximations whose limit, as $\epsilon\to0$ and $H\to\infty$, gives the pacing equilibrium of Theorem 1.
--
--   **Formalization Note** The artificial good gives buyer $i$ the value $2\alpha_i\epsilon\le2\epsilon$, which is why the bound reads $\sum_j v_{ij}+2\epsilon\le M$. Definition 3 assumes $H>0$; this follows from $H>M/\epsilon$ whenever there is a buyer (then $M\ge2\epsilon>0$), and with no buyer the conclusion holds trivially, so it is not a separate hypothesis.
--
--   Differences from the source:
--   - encoding: "M any upper bound on the sum of a buyer's valuations, including those for the artificial good" → `∀ i, ∑ j, v i j + 2ε ≤ M`; reason: the artificial good is worth $2\epsilon$ per unit and a buyer receives at most one unit.
--   - encoding: Definition 3's standing $H>0$ → not a hypothesis; reason: implied by $H>M/\epsilon$ when there is a buyer, and the conclusion is trivial when there is none.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 11 (PDF 11), Theorem 2

import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2 {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] (P : PacingGame N G)
    (ε H M : ℝ) (hε : 0 < ε) (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) :
    ∃ α : N → ℝ, IsSmoothedPNE P ε H α := by sorry

end MultPacing.Existence
