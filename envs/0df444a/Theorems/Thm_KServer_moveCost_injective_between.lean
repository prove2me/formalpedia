-- Prove2me | Theorems.Thm_KServer_moveCost_injective_between
-- name    : KServer.moveCost_injective_between
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:12:50.409558+00:00
-- url     : https://prove2.me/theorems/9d83fb6f-ce7a-4e8a-901f-ecc2816da80d
-- title:
--   Every configuration covering a request has an injective one between it and any injective target
-- statement:
--   Let $M$ be a metric space, $k$ a number of servers, and recall that a configuration is a map $Y:\{1,\dots,k\}\to M$ with movement cost $d(Y,Z)=\sum_i d(Y_i,Z_i)$. Call $Y$ *injective* when its $k$ servers occupy $k$ distinct points.
--
--   **Statement.** Let $Z$ be injective, let $r\in M$, and let $Y$ be any configuration with a server on $r$. Then there is an **injective** configuration $Y'$, still with a server on $r$, lying between $Y$ and $Z$:
--   $$d(Y,Y')+d(Y',Z)\;\le\;d(Y,Z).$$
--
--   **Role.** The classical $k$-server problem takes a configuration to be a set of $k$ points, so the question of two servers sharing a point never arises. In a model whose configurations are labelled maps it does, and it is a genuine obstruction: the work function's increments behave differently at degenerate configurations, and the classical bounds on the total growth of the work function are proved only for the honest, $k$-point ones.
--
--   This lemma is what makes the difference harmless where it matters. Because the work function is $1$-Lipschitz, betweenness upgrades to
--   $$w(Y')+d(Y',Z)\;\le\;w(Y)+d(Y,Z),$$
--   so in the one-step recurrence
--   $$w_{\sigma r}(Z)=\inf\bigl\{w_\sigma(Y)+d(Y,Z)\ :\ r\in Y\bigr\}$$
--   the infimum over *all* configurations covering $r$ agrees with the infimum over the **injective** ones, as soon as the target $Z$ is injective. Consequently the Work Function Algorithm, started at an injective configuration, can be made to stay injective forever, and its analysis only ever needs the work function's behaviour at $k$-point configurations.
--
--   **Proof sketch.** Induct on the number of coordinates where $Y$ and $Z$ differ. If $Y$ is already injective there is nothing to do. Otherwise two indices $a\ne b$ carry the same point; since $Z$ is injective, $Z_a\ne Z_b$, so at least one of them — say $j$ — has $Y_j\ne Z_j$. Move that one server directly to its target, $Y_1=Y[j\mapsto Z_j]$. The point $Y_j$ is still occupied by the other index, so $Y_1$ still covers $r$; the number of differing coordinates drops by one; and the move is exactly on the geodesic, $d(Y,Y_1)+d(Y_1,Z)=d(Y,Z)$. The induction terminates, at worst at $Z$ itself.
--
--   **Formalization Note** The hypothesis that $Z$ is injective cannot be dropped: with $Z$ degenerate, no injective configuration need lie between $Y$ and $Z$. The proof is by induction on the cardinality of `Finset.univ.filter (fun i => Y i ≠ Z i)`, and the two movement-cost computations — the cost of a single-coordinate update, and the effect of that update on the cost to `Z` — are both instances of the fact that sums agreeing off one index differ by that index's contribution.
-- source:
--   Model infrastructure for the labelled-configuration formulation of the k-server problem; the classical treatment takes configurations to be k-point sets, as in E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 1.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem moveCost_injective_between (k : ℕ) (M : Type) [MetricSpace M]
    (Y Z : Config k M) (hZ : Function.Injective Z) (r : M) (hY : ∃ i, Y i = r) :
    ∃ Y' : Config k M, Function.Injective Y' ∧ (∃ i, Y' i = r) ∧
      moveCost Y Y' + moveCost Y' Z ≤ moveCost Y Z := by sorry

end KServer
