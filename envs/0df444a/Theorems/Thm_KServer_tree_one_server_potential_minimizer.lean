-- Prove2me | Theorems.Thm_KServer_tree_one_server_potential_minimizer
-- name    : KServer.tree_one_server_potential_minimizer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T21:55:39.511353+00:00
-- url     : https://prove2.me/theorems/2e67973f-99b0-4b89-8059-56a3aa085c2e
-- title:
--   On a tree the one-server potential is realized by any minimizer of w(u) - d(c,u)
-- statement:
--   For a single server on a tree, the Coester--Koutsoupias potential of a work function $w$ is
--
--   $$\Phi(w) \;=\; \min_{y} \bigl( w(y) + w(\bar y) \bigr) \;=\; \min_{y, z} \bigl( w(y) + w(z) + \Delta - d(y,z) \bigr),$$
--
--   where $\bar y$ denotes the antipode of $y$ and $\Phi_x(w) = w(x) + w(\bar x) = \min_z (w(x) + w(z) + \Delta - d(x,z))$ is the term of the potential anchored at $x$. The lemma says that on a tree the anchor may be chosen by a *one-dimensional* greedy rule: for any fixed vertex $c$,
--
--   $$x \in \arg\min_u \bigl( w(u) - d(c,u) \bigr) \;\Longrightarrow\; \Phi(w) = \Phi_x(w).$$
--
--   The theorem is stated in the equivalent unfolded form: for every pair $y, z$,
--
--   $$\min\bigl( w(x) + w(z) + \Delta - d(x,z),\; w(x) + w(y) + \Delta - d(x,y) \bigr) \;\le\; w(y) + w(z) + \Delta - d(y,z).$$
--
--   Both terms on the left are candidate values of $\Phi_x(w)$, so the inequality says $\Phi_x(w)$ is at most every value competing in the minimum defining $\Phi(w)$, whence $\Phi_x(w) \le \Phi(w)$; the reverse inequality is immediate because $\Phi$ is a minimum over anchors.
--
--   ## Role
--
--   This is Lemma 24 of Coester and Koutsoupias, the first step of their proof that the Work Function Algorithm is $3$-competitive for three servers on trees. Its point is that the anchor of the potential need not be searched for: it is pinned down by minimising the far simpler expression $w(u) - d(c,u)$, with $c$ an arbitrary reference vertex. Their subsequent lemma on swapping the first two anchors --- and, through it, the whole tree argument --- uses exactly this freedom in the choice of $c$.
--
--   The hypothesis that carries the argument is that the metric is a tree, in the form of the four-point condition: for any four points, $d(c,x) + d(y,z)$ is at most the larger of the two other pairings $d(c,y) + d(x,z)$ and $d(c,z) + d(x,y)$. Equivalently, $-d$ is quasiconvex on two-point sets, which Coester and Koutsoupias show characterises tree metrics among all metrics; it is the property their tree argument depends on throughout.
--
--   ## Formalization note
--
--   `IsTreeVertexSpace M` says the metric on $M$ is realised by the path metric of a weighted tree whose vertex set is $M$ itself. The four-point condition is available for such spaces. The function $w$ is unconstrained --- neither $1$-Lipschitzness nor any work-function property is used --- and $\Delta$ enters only as an additive constant common to all four expressions, so the theorem is a statement about arbitrary real functions on a tree; this is why it applies unchanged to the restriction $w(\,\cdot\,x_2 \dots x_k)$ of a $k$-server work function, which is how it is invoked in the tree analysis.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section on trees, Lemma 24 (lem:k1arbitraryMinimizer).

import Mathlib
import Definitions.Def_KServer_tree_metric

namespace KServer

theorem tree_one_server_potential_minimizer (M : Type) [MetricSpace M] [Fintype M]
    (hM : IsTreeVertexSpace M) (w : M → ℝ) (Δ : ℝ) (c x : M)
    (hx : ∀ u : M, w x - dist c x ≤ w u - dist c u) (y z : M) :
    min (w x + w z + Δ - dist x z) (w x + w y + Δ - dist x y)
      ≤ w y + w z + Δ - dist y z := by sorry

end KServer
