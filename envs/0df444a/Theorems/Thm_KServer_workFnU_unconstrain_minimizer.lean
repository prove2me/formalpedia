-- Prove2me | Theorems.Thm_KServer_workFnU_unconstrain_minimizer
-- name    : KServer.workFnU_unconstrain_minimizer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T22:48:19.23981+00:00
-- url     : https://prove2.me/theorems/d99398cb-88e7-4475-ae2f-efa5bdf1c11e
-- title:
--   A cheapest configuration serving a request becomes globally cheapest by moving that one server
-- statement:
--   Let $w$ be the (unlabelled) work function of a $k$-server instance, let $Y$ minimise $w$ among the configurations containing a given point $r$, and let $Z$ be a minimiser of $w$ over all configurations. Then there is a point $z$ such that
--
--   $$Y - r + z \quad\text{is a minimiser of } w \text{ over all configurations.}$$
--
--   That is: a cheapest configuration serving $r$ is turned into a cheapest configuration outright by moving the single server that stands on $r$, and every other server stays where it is.
--
--   ## Role
--
--   This is the case $|A| = 1$ of the greedy lemma for quasiconvex set functions --- Lemma 13 of Coester and Koutsoupias, in the tradition of Dress and Wenzel's analysis of the greedy algorithm on valuated matroids. It is the converse direction of the substitution lemma: substitution passes from an unconstrained minimiser to a constrained one, this passes back. Coester and Koutsoupias use it in their tree argument to identify a minimiser of $X \mapsto w(X) - d(X, x_2^2)$ with a configuration in which a copy of $\bar x_2$ has been resolved to a point $x_1$, which is what licenses the subsequent exchange of the first two anchors of their potential.
--
--   For a general constraint set $A$ the lemma requires the greedy exchange induction: one chooses a constrained minimiser whose difference from the unconstrained one is minimal and derives a contradiction from any remaining discrepancy. For $|A| = 1$ no induction is needed. A single application of quasiconvexity to the pair $(Y, Z)$, splitting off exactly the coordinate on which $Y$ carries $r$, produces two hybrids: $Y - r + z$ with $z$ the point $Z$ contributes at that coordinate, and a configuration that still contains $r$ and is therefore bounded below by $w(Y)$ by the constrained minimality of $Y$. Cancelling leaves $w(Y - r + z) \le w(Z)$, and $Z$ is a global minimum.
--
--   ## Formalization note
--
--   Configurations are functions $\mathrm{Fin}\,k \to M$; $Y - r + z$ is `Function.update Y j z`, where $j$ is a coordinate at which $Y$ takes the value $r$. Quasiconvexity of `workFnU` is used in its pairing form: for any two configurations there is a permutation aligning them such that every splitting of the coordinates into two blocks yields hybrids whose values sum to at most the sum of the originals. No finiteness or compactness hypothesis on the metric space is needed; the existence of the two minimisers is assumed rather than derived, so the statement is available whenever they exist.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Lemma 13 (the greedy lemma for quasiconvex functions), specialised to a one-point constraint; cf. A. Dress, W. Wenzel, 'Valuated matroids: a new look at the greedy algorithm', Applied Mathematics Letters 3 (1990).

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_unconstrain_minimizer (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Y : Config k M) (j : Fin k) (hj : Y j = r)
    (hY : ∀ W : Config k M, (∃ l, W l = r) → workFnU C₀ σ Y ≤ workFnU C₀ σ W)
    (Z : Config k M) (hZ : ∀ W : Config k M, workFnU C₀ σ Z ≤ workFnU C₀ σ W) :
    ∃ z : M, ∀ W : Config k M,
      workFnU C₀ σ (Function.update Y j z) ≤ workFnU C₀ σ W := by sorry

end KServer
