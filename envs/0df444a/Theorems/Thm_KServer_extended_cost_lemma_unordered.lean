-- Prove2me | Theorems.Thm_KServer_extended_cost_lemma_unordered
-- name    : KServer.extended_cost_lemma_unordered
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:41:14.454676+00:00
-- url     : https://prove2.me/theorems/eda0a72f-6ea0-4356-a001-9d5e4c49ad23
-- title:
--   Extended Cost Lemma for the unordered work function
-- statement:
--   Fix a metric space $M$, a number $k\ge1$ of servers and an initial configuration $C_0$, and write $\widehat w_t=\widehat w(C_0;r_1,\dots,r_t;\cdot)$ for the *unordered* work function after the first $t$ requests of a sequence $\sigma$.
--
--   **Statement.** Let $\lambda$ and $c$ be constants. Suppose that for every request sequence $\sigma$ of length $m$ there are numbers $u_1,\dots,u_m$ such that
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\quad\text{for every configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;\lambda\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--   Then there is an online algorithm starting at $C_0$ which is $(\lambda-1)$-competitive.
--
--   **Role.** This is the lemma of Chrobak and Larmore, stated for the unordered work function, and it is the hinge of the modern theory of the $k$-server problem: to bound the competitive ratio of the Work Function Algorithm one never reasons about the algorithm's configurations, only about the total growth
--   $$\sum_{t=1}^{m}\max_X\bigl\{\widehat w_t(X)-\widehat w_{t-1}(X)\bigr\}$$
--   of the work function. Taking $\lambda=k+1$ would prove the $k$-server conjecture; $\lambda=2k$ is what Koutsoupias and Papadimitriou established, giving the ratio $2k-1$; $\lambda=3$ for $k=2$, and $\lambda=k+1$ on spaces of $k+1$ or $k+2$ points, give the known tight cases.
--
--   **Why the unordered work function.** The companion statement `KServer.extended_cost_lemma` is the same lemma for the labelled work function `workFn`, and is also true; but its hypothesis is much stronger, and in fact fails for the classical values of $\lambda$. On the uniform metric space of $k+1$ points with $k=2$ the labelled total growth equals $4\cdot\mathrm{OPT}$ while the unordered one equals $3\cdot\mathrm{OPT}$, and the gap accumulates linearly in the length of the request sequence rather than being absorbed into an additive constant. So it is this version that the four classical upper bounds are applied through.
--
--   **The algorithm.** The algorithm produced is the *Work Function Algorithm*: at step $t$ it moves from $C_{t-1}$ to a configuration $C_t$ containing $r_t$ which (almost) minimises $\widehat w_{t-1}(X)+d(C_{t-1},X)$. Its step cost is then rewritten as a term bounded by $u_t$ minus a term that telescopes; what survives the telescoping is $-\widehat w_m(C_m)\le-\mathrm{OPT}$, which is where the $\lambda-1$ comes from.
--
--   **Formalization Note** The hypothesis is stated with an explicit bounding sequence $u$ rather than with $\max_X\{\widehat w_t(X)-\widehat w_{t-1}(X)\}$, because on an unbounded metric space that maximum ranges over an infinite family and its finiteness is a separate fact; any bound on it gives an admissible $u$, so the two forms have the same strength. The prefix $r_1,\dots,r_t$ appears as `σ.take t`. On a general metric space the minimiser defining the Work Function Algorithm need not exist, so the algorithm is built from approximate minimisers with error $2^{-t}$ at step $t$; the total slack is at most $1$ and is absorbed into the additive constant, which comes out as $c+1$. Note that the recurrence used, $\widehat w_t(Z)=\inf\{\widehat w_{t-1}(Y)+d(Y,Z) : r_t\in Y\}$, holds with the *labelled* movement cost `moveCost` even though both work functions are unordered, since a relabelling can be transferred from one argument of `moveCost` to the other.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, Lemma 2 (Extended Cost Lemma) together with equation (7); originally M. Chrobak, L. Larmore, The server problem and on-line games, in: On-line Algorithms, DIMACS Series in Discrete Mathematics and Theoretical Computer Science 7 (1992) 11-64.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem extended_cost_lemma_unordered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by sorry

end KServer
