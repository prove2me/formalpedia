-- Prove2me | Theorems.Thm_KServer_workFn_workFnU_sandwich
-- name    : KServer.workFn_workFnU_sandwich
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T21:41:33.679462+00:00
-- url     : https://prove2.me/theorems/0d828657-0a49-4182-934b-ed9826632c65
-- title:
--   The labelled and unlabelled work functions differ by at most k times the diameter
-- statement:
--   For a $k$-server instance there are two work functions that differ in how the final configuration is presented. The **labelled** work function $w(X)$ charges an offline solution for delivering server $i$ to the point $X_i$, so it depends on how the target configuration is labelled; the **classical**, or unlabelled, work function $w^{\mathrm U}(X)$ of Koutsoupias and Papadimitriou depends only on the multiset of occupied points, the final move being a minimum-cost matching, and is recovered as
--
--   $$w^{\mathrm U}(X) \;=\; \min_{\pi \in \mathfrak S_k} w(X \circ \pi).$$
--
--   These two are genuinely different functions --- already for $k = 2$ and the empty request sequence, $w$ at the transposed initial configuration is $2\,d$ while $w^{\mathrm U}$ there is $0$. The theorem says they are nevertheless never far apart: if $\Delta$ bounds the diameter of the metric space, then for every request sequence and every configuration $X$,
--
--   $$w^{\mathrm U}(X) \;\le\; w(X) \;\le\; w^{\mathrm U}(X) + k\Delta.$$
--
--   ## Role
--
--   The classical theory --- quasiconvexity, the Koutsoupias--Papadimitriou duality, the extended-cost bounds behind the $(2k-1)$-competitiveness of the Work Function Algorithm and behind the potential method of Coester and Koutsoupias --- is developed for $w^{\mathrm U}$. Formal developments, on the other hand, find the labelled $w$ the more convenient primitive, since a configuration is naturally a function $\{1,\dots,k\\} \to M$ and movement cost is a sum over server indices. The sandwich is the bridge between the two: it says that on a bounded metric space the difference is an additive constant depending only on the space, so any statement about $w^{\mathrm U}$ that tolerates an additive constant --- competitiveness, in particular, is defined up to exactly such a constant --- transfers to $w$ *pointwise*.
--
--   What the sandwich does **not** transfer is anything about *increments*. The quantity that drives the analysis of the Work Function Algorithm is the extended cost $\max_X\bigl(w'(X) - w(X)\bigr)$ over one request, and a bound of $k\Delta$ on $w - w^{\mathrm U}$ says nothing useful about it once the increments are summed over a long request sequence. So the sandwich is sharp in the sense that matters: it settles the pointwise comparison completely and leaves the dynamic comparison open.
--
--   ## Formalization note
--
--   The bound $\Delta$ is supplied as a hypothesis $\forall u\,v,\ d(u,v) \le \Delta$ rather than as `Metric.diam`, which avoids boundedness side conditions; no sign hypothesis on $\Delta$ is needed. The lower bound is the instance $\pi = \mathrm{id}$ of the infimum defining $w^{\mathrm U}$; the upper bound applies $1$-Lipschitzness of $w$ to each relabelling $X \circ \pi$, whose movement cost from $X$ is a sum of $k$ distances and hence at most $k\Delta$, and then takes the infimum over $\pi$.
-- source:
--   Folklore comparison between the labelled work function and the classical work function of E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995); the classical (unlabelled) work function is the one used in E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), and in C. Coester, E. Koutsoupias, ICALP 2021.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFn_workFnU_sandwich (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) (Δ : ℝ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) :
    workFnU C₀ σ X ≤ workFn C₀ σ X ∧ workFn C₀ σ X ≤ workFnU C₀ σ X + k * Δ := by sorry

end KServer
