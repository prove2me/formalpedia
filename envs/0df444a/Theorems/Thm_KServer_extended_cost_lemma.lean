-- Prove2me | Theorems.Thm_KServer_extended_cost_lemma
-- name    : KServer.extended_cost_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:21:02.123019+00:00
-- url     : https://prove2.me/theorems/6e8c29e0-594f-4701-8d0e-bb421fa2e72a
-- title:
--   Extended Cost Lemma: bounding the growth of the work function bounds the competitive ratio
-- statement:
--   Fix a metric space $M$, a number $k\ge1$ of servers and an initial configuration $C_0$, and write $w_t=w(C_0;r_1,\dots,r_t;\cdot)$ for the work function after the first $t$ requests of a sequence $\sigma$.
--
--   **Statement.** Let $\lambda$ and $c$ be constants. Suppose that for every request sequence $\sigma$ of length $m$ there are numbers $u_1,\dots,u_m$ such that
--   $$w_t(X)\;\le\;w_{t-1}(X)+u_t\quad\text{for every configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;\lambda\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--   Then there is an online algorithm starting at $C_0$ which is $(\lambda-1)$-competitive.
--
--   **Role.** This is the lemma of Chrobak and Larmore that converts a statement *purely about work functions* into a competitive ratio, and it is the hinge of the modern theory of the $k$-server problem. Its consequence is striking: to bound the competitive ratio of the Work Function Algorithm one never has to reason about the algorithm's configurations at all — it suffices to bound the total growth
--   $$\sum_{t=1}^{m}\max_X\bigl\{w_t(X)-w_{t-1}(X)\bigr\}$$
--   of the work function against the offline optimum. Taking $\lambda=k+1$ would prove the $k$-server conjecture; $\lambda=2k$ is what Koutsoupias and Papadimitriou established, giving the ratio $2k-1$; $\lambda=3$ for $k=2$, and $\lambda=k+1$ on spaces of $k+1$ or $k+2$ points, give the known tight cases. Every one of those results is exactly one application of this lemma.
--
--   **The algorithm.** The online algorithm produced is the *Work Function Algorithm*: at step $t$ it moves from $C_{t-1}$ to a configuration $C_t$ containing $r_t$ which (almost) minimises $w_{t-1}(X)+d(C_{t-1},X)$. The one-step recurrence identifies that minimum with $w_t(C_{t-1})$, which gives the algorithm's characteristic identity $w_t(C_{t-1})=w_{t-1}(C_t)+d(C_{t-1},C_t)$: the online algorithm moves *against* an optimal offline algorithm. Its step cost is then rewritten as a term bounded by $u_t$ minus a term that telescopes, and what survives the telescoping is $-w_m(C_m)\le-\mathrm{OPT}$, which is where the $\lambda-1$ comes from.
--
--   **Formalization Note** The hypothesis is stated with an explicit bounding sequence $u$ rather than with $\max_X\{w_t(X)-w_{t-1}(X)\}$, because on an unbounded metric space that supremum is a supremum of an unbounded index set and its finiteness is a separate (true, but irrelevant) fact; any bound on it gives an admissible $u$, so the two forms have the same strength. The prefix $r_1,\dots,r_t$ appears as `σ.take t`. On a general metric space the minimiser defining the Work Function Algorithm need not exist, so the algorithm is built from approximate minimisers with error $2^{-t}$ at step $t$; the total slack is at most $1$ and is absorbed into the additive constant, which comes out as $c+1$.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, Lemma 2 (Extended Cost Lemma) together with equation (7); originally M. Chrobak, L. Larmore, The server problem and on-line games, in: On-line Algorithms, DIMACS Series in Discrete Mathematics and Theoretical Computer Science 7 (1992) 11-64.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem extended_cost_lemma (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFn C₀ (σ.take (t + 1)) X ≤ workFn C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by sorry

end KServer
