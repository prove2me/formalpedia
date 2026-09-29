-- Prove2me | Theorems.Thm_KServer_offline_avg_bound
-- name    : KServer.offline_avg_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:09:06.937634+00:00
-- url     : https://prove2.me/theorems/ac9792b5-bf66-4c7c-9f9a-5f4a18d119d8
-- title:
--   The $k$ offline algorithms: their total cost is the walk traced by the requests
-- statement:
--   Work in a metric space $M$ with $k\ge 1$ servers, fix a set $P\subseteq M$ of exactly $k+1$ distinct points, and fix an initial configuration $C_0$ of the $k$ servers. For a request sequence $\sigma=(r_1,\dots,r_n)$, write $\mathrm{OPT}(C_0,\sigma)$ for the optimal offline cost: the least total movement of a schedule that starts at $C_0$ and places a server on $r_j$ at step $j$, chosen with the whole of $\sigma$ known in advance.
--
--   **Statement.** There is a constant $D$, depending on $P$ and $C_0$ but *not* on the request sequence, such that for every $\sigma$ whose requests all lie in $P$,
--   $$k\cdot\mathrm{OPT}(C_0,\sigma)\;\le\;\sum_{j=1}^{n-1} d(r_j,r_{j+1})\;+\;D.$$
--
--   **Role.** This is the counting trick at the heart of the Manasse--McGeoch--Sleator lower bound, stated on its own. Rather than comparing an online algorithm against a single offline algorithm, one compares it against $k$ of them at once. On a subspace of $k+1$ points there are exactly $k+1$ configurations that occupy $k$ distinct points, each determined by the single point it leaves uncovered; one keeps $k$ offline algorithms in $k$ pairwise different such configurations, so that at every moment exactly one point of $P$ is covered by all of them. Whichever point of $P$ is requested, at most one of the $k$ algorithms fails to cover it, and it restores the invariant by moving a server from that commonly covered point onto the request. Consequently exactly one offline algorithm moves per request, and it moves precisely the distance from the previous request to the current one, so the $k$ offline costs add up to the length of the walk traced by the requests. Getting the $k$ algorithms into their initial configurations from the common starting configuration $C_0$ costs a fixed amount that depends only on $C_0$ and $P$; that, together with the very first step, is what the additive constant $D$ absorbs.
--
--   Since each of the $k$ algorithms is a legitimate offline schedule starting at $C_0$, each of their costs is at least $\mathrm{OPT}(C_0,\sigma)$, and averaging turns the displayed identity into the stated inequality: the optimum is at most a $1/k$ fraction of the walk length. Paired with a lower bound on the online cost by the same walk length, this is what produces the competitive ratio $k$.
--
--   **Formalization Note** Consecutive pairs of the request list are taken as `σ.zip σ.tail`, so the displayed sum is the sum of `dist p.1 p.2` over that list of pairs; for a list of length $n$ it has $n-1$ entries, and is empty when $\sigma$ is empty or a singleton. The offline optimum is the infimum over schedules, `offlineCost`, taken from the shared model file.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, preprint https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf, Section 3.1, proof of Theorem 1: "Instead of comparing algorithm A against one offline algorithm, we compare its cost against k distinct offline algorithms so that the cost of the online algorithm is equal to the total cost of all k offline algorithms", including the fixed initial cost of moving the offline algorithms into the k pairwise different configurations; originally Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W, Theorem 6 (and Corollary 7).

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem offline_avg_bound (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (P : Finset M) (hP : P.card = k + 1) (C₀ : Config k M) :
    ∃ D : ℝ, ∀ σ : List M, (∀ r ∈ σ, r ∈ P) →
      (k : ℝ) * offlineCost C₀ σ
        ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum + D := by sorry

end KServer
