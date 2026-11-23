-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_Supplement_theorem_3
-- name    : LargeCongestion.Poisson.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:33:52.6918+00:00
-- url     : https://prove2.me/theorems/3b83dd4b-0903-4265-990a-3c0253e296fe
-- title:
--   Theorem 3 — Poisson congestion equilibrium iff Wardrop equilibrium for the same induced flow
-- statement:
--   Let $S_t$ be the finite nonempty feasible resource-subset families. Let the integer-load resource costs $c_e$ be nonnegative and weakly increasing at positive loads. Let $d_t>0$, and assume (18): for some real $\nu,d_{\max}$, $\sum_td_t<d_{\max}$ and the Poisson expectation of $|\Delta^2c_e(1+V)|$ at $V\sim\mathrm{Poisson}(d_{\max})$ is at most $\nu$ for every resource.
--
--   For any type-symmetric mixed strategy $q_t\in\Delta(S_t)$, construct $y_{t,s}=d_tq_t(s)$ and $x_e=\sum_{t,s\in S_t}y_{t,s}\mathbf1_{\{e\in s\}}$. In the population game, populations are independent Poisson variables with means $d_t$, an active player uses the Palm posterior, and action costs are exactly $\sum_{e\in s}c_e(1+X_e^{-t})$. Then
--   $$q\text{ is a Poisson-game equilibrium}\quad\Longleftrightarrow\quad(y,x)\in\operatorname{WE}(\breve\Gamma^\infty),\qquad \breve c_e(x)=\mathbb E[c_e(1+\mathrm{Poisson}(x))].$$
--   The equivalence relates the same profile and its computed flows in both directions. It supplies the population-game interpretation of the auxiliary nonatomic game in the goal.
--
--   Differences from the source:
--   - encoding: a type mixed strategy on S_t → a probability vector on the subtype of feasible resource subsets, with induced flows zero off S_t; reason: this is the same finite simplex; nonempty strategy sets are explicit
--   - reading: printed real-valued cost and moment-bound glyphs → c_e maps natural loads to real costs, and nu is real; reason: the Poisson expectations and (18) use real values; c_e(0) is never evaluated
--   - encoding: finite expectations in (18) and (25) → Summable guards in (18) and in equilibrium membership for every expected cost; reason: divergent real tsum defaults to zero; (18) guarantees the required well-defined expectations, which are not assumed separately
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, Theorem 3, p. 23

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_PoissonCongestion

namespace LargeCongestion.Poisson.Supplement

theorem theorem_3 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S)
    (c : E → ℕ → ℝ) (hc : IsCostFamily c)
    (d : T → ℝ) (hd : ∀ t, 0 < d t) (nu dmax : ℝ) (h18 : Condition18 c d nu dmax)
    (q : ∀ t, CongestionAction S t → ℝ) (hq : IsTypeProfile q) :
    (poissonGame d (congestionCost S c)).IsEquilibrium q ↔
      IsWardrop S (cBreve c) d (inducedFlow S d q) (inducedLoad S d q) := by sorry

end LargeCongestion.Poisson.Supplement
