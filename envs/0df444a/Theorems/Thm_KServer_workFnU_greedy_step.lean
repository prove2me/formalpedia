-- Prove2me | Theorems.Thm_KServer_workFnU_greedy_step
-- name    : KServer.workFnU_greedy_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T21:49:57.784531+00:00
-- url     : https://prove2.me/theorems/a95774d7-81cf-48a4-bebe-f40cd7cd75d6
-- title:
--   A cheapest configuration serving a request is one server-move from a cheapest configuration
-- statement:
--   Let $w$ be the (unlabelled) work function of a $k$-server instance, and let $X$ be a configuration minimising $w$ over all configurations. Let $r$ be a point of the metric space. Then for every configuration $Y$ containing $r$ there is an index $i$ with
--
--   $$w\bigl(X - x_i + r\bigr) \;\le\; w(Y).$$
--
--   Equivalently, since each $X - x_i + r$ contains $r$,
--
--   $$\min_{Y \ni r} w(Y) \;=\; \min_{i} \; w\bigl(X - x_i + r\bigr):$$
--
--   **a cheapest configuration serving $r$ can be obtained from a cheapest configuration overall by moving a single server to $r$.**
--
--   ## Role
--
--   This is the case $|A| = 1$ of the substitution lemma for quasiconvex set functions --- Lemma 12 of Coester and Koutsoupias, itself a descendant of the exchange property that Dress and Wenzel isolated for valuated matroids and that Koutsoupias and Papadimitriou introduced into the $k$-server problem under the name quasiconvexity. The general statement says that among the minimisers of $w$ subject to containing a prescribed multiset $A$ of fewer than $k$ points, one can be found inside $X \cup A$; the case $|A| = 1$ is the one the analysis of the Work Function Algorithm uses at every request, since a request is a single point.
--
--   The general case genuinely needs the greedy/exchange induction of Dress and Wenzel: one picks a constrained minimiser $Y$ whose difference from $X$ is minimal and derives a contradiction from any remaining discrepancy. For $|A| = 1$ that machinery is unnecessary. A single application of quasiconvexity to the pair $(X, Y)$, splitting off exactly the coordinate at which $Y$ holds $r$, produces the two configurations $X - x_i + r$ and $Y - r + x_i$; the second is compared to $X$ by global minimality, and the first inequality falls out. In particular the statement holds with no finiteness or compactness hypothesis on the metric space, and no assumption that a constrained minimiser exists.
--
--   ## Formalization note
--
--   Configurations are functions $\mathrm{Fin}\,k \to M$ and $w$ is `workFnU`, the work function of the *unlabelled* configuration, obtained from the labelled one by minimising over relabellings; quasiconvexity is available for it in the pairing form: for any two configurations there is a permutation $\pi$ aligning them such that *every* splitting of the coordinates into two blocks yields a pair of hybrids whose $w$-values sum to at most $w(X) + w(Y)$. The proof above is the instance in which the block is the complement of the single coordinate carrying $r$. The replacement $X - x_i + r$ is `Function.update X i r`.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Lemma 12 (the substitution lemma for quasiconvex functions), specialised to a one-point constraint; the quasiconvexity notion is from E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995), and A. Dress, W. Wenzel, 'Valuated matroids: a new look at the greedy algorithm', Applied Mathematics Letters 3 (1990).

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_greedy_step (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M)
    (hX : ∀ Z : Config k M, workFnU C₀ σ X ≤ workFnU C₀ σ Z)
    (r : M) (Y : Config k M) (hY : ∃ j, Y j = r) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) ≤ workFnU C₀ σ Y := by sorry

end KServer
