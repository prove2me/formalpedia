-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_1
-- name    : MultPacing.Existence.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:53.73463+00:00
-- url     : https://prove2.me/theorems/36b791cd-375f-4775-afab-5a2603c6027f
-- title:
--   Theorem 1, p. 11 — every pacing game admits a second price pacing equilibrium
-- statement:
--   Let $N$ be a finite set of buyers and $G$ a finite set of divisible goods, each sold in a second price auction. Each buyer $i$ has valuations $v_{ij}\ge0$ and a budget $B_i>0$. Then the pacing game has a second price pacing equilibrium: there are pacing multipliers $\alpha\in[0,1]^N$, allocations $x_{ij}\in[0,1]$ and prices $p_j$ such that
--
--   1. $\sum_i x_{ij}\le1$ for every good $j$, with equality when some $v_{ij}>0$;
--   2. $x_{ij}>0$ implies $\alpha_i v_{ij}\ge\alpha_k v_{kj}$ for every $k$;
--   3. $x_{ij}>0$ implies $p_j=\max_{k\ne i}\alpha_k v_{kj}$ (and $p_j=0$ if $i$ is the only buyer);
--   4. $\sum_j p_j x_{ij}\le B_i$ for every buyer $i$;
--   5. $\sum_j p_j x_{ij}<B_i$ implies $\alpha_i=1$.
--
--   In short,
--   $$
--   \text{every pacing game } (v\ge0,\ B>0)\ \text{admits } (\alpha,x,p)\ \text{with } (\alpha,x,p)\ \text{an SPPE}.
--   $$
--   The result holds for all finite numbers of buyers and goods and all valuations, with no genericity or tie assumption. It shows that the budget-management rule of multiplicative pacing always has a stable outcome in which every buyer best responds (Proposition 2 of the paper) and the market clears.
--
--   Differences from the source:
--   - encoding: buyers $\{1,\dots,n\}$ and goods $\{1,\dots,m\}$ → arbitrary finite types `N`, `G`; reason: the same instances up to relabelling.
--   - encoding: "the per-unit price $p_j$" → a price vector $p$ quantified with $\alpha$ and $x$ and pinned to the highest other bid wherever $x_{ij}>0$, with $s_{ij}=p_jx_{ij}$; reason: Definition 2 names $p_j$ without quantifying it, and an unpinned $p_j$ only multiplies allocations equal to $0$.
--   - encoding: "the highest bid $\alpha_{i'}v_{i'j}$ other than $i$'s bid" → the maximum over $k\ne i$, $0$ when there is no other buyer; reason: bids are nonnegative, and the paper gives a lone bidder price $0$ (p. 16).
--   - encoding: budgets $B_i>0$ → real numbers $B_i>0$; reason: §3's model has finite budgets; $B_i=\infty$ appears only in examples outside the model.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 11 (PDF 11), Theorem 1 (with Definition 2, p. 9)

import Mathlib
import Definitions.Def_MultPacing_Existence_Model

namespace MultPacing.Existence

theorem theorem_1 {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] (P : PacingGame N G) :
    ∃ (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ), IsSPPE P α x p := by sorry

end MultPacing.Existence
