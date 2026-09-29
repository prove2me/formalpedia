-- Prove2me | Theorems.Thm_KServer_lazy_schedule
-- name    : KServer.lazy_schedule
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:47:38.100509+00:00
-- url     : https://prove2.me/theorems/ba6fb6e4-8608-4b88-9669-b2a8bf7193a2
-- title:
--   Every offline schedule can be made lazy without increasing its cost
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$ and a target configuration $X$. Call a schedule **lazy** if it serves each request by moving a single server directly onto it, leaving every other server where it stands.
--
--   **Statement.** Every schedule $S$ serving $\sigma$ from $C_0$ can be replaced by a lazy schedule $S'$ serving $\sigma$ from $C_0$ whose cost, including a final move to $X$, is no larger:
--   $$\sum_{j}d\bigl(S'_j,S'_{j+1}\bigr)+d\bigl(S'_n,X\bigr)\;\le\;\sum_{j}d\bigl(S_j,S_{j+1}\bigr)+d\bigl(S_n,X\bigr).$$
--
--   **Role.** Laziness is the normal form in which the classical picture of the work function is drawn. Once every schedule may be assumed lazy, an offline solution is literally $k$ *paths*: server $i$ starts at $C_0(i)$, visits in order the requests it serves, and ends at $X(i)$ — with each request an interior node of exactly one path, entered once and left once. That is the picture in which the quasiconvexity of the work function is proved, by an alternating-path argument between the path systems of two targets; without laziness the two systems share no nodes and the argument has nothing to alternate on.
--
--   Because the target $X$ appears in the statement, the normalisation applies verbatim to the work function: taking the infimum over $S$ on both sides shows $w(C_0;\sigma;X)$ is unchanged if the competing schedules are restricted to lazy ones.
--
--   **Proof sketch.** Build $S'$ step by step, always moving the server whose index $S$ itself places on the current request, and measure the discrepancy by the potential $\Phi_j=d(S'_j,S_j)$. A single step satisfies
--   $$d\bigl(S'_j,S'_{j+1}\bigr)+\Phi_{j+1}\;\le\;\Phi_j+d\bigl(S_j,S_{j+1}\bigr),$$
--   by the triangle inequality applied coordinatewise: the moved server travels from $S'_j(i)$ to the request, which is where $S_{j+1}(i)$ already is, and every other coordinate is unchanged in $S'$. Summing telescopes $\Phi$ away, with $\Phi_0=0$ because both schedules start at $C_0$, and the final $\Phi_n$ is absorbed by the triangle inequality into the move to $X$.
--
--   **Formalization Note** Laziness is stated as `S' (j+1) = Function.update (S' j) i (σ.get j)`, which also covers the case where the request is already served — the index chosen is then one already standing on it, and the move costs nothing. The schedule is defined by ordinary recursion on the step index, the moved index being chosen once and for all by `choose` from the serving condition on `S`.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3 (the graphical description of work functions as k directed paths through the requests); the laziness normalisation is standard, see also E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem lazy_schedule (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M)
    (S : ℕ → Config k M) (hS : ServesFrom C₀ σ S) :
    ∃ S' : ℕ → Config k M, ServesFrom C₀ σ S' ∧
      (∀ j : Fin σ.length, ∃ i : Fin k, S' (j + 1) = Function.update (S' j) i (σ.get j)) ∧
      (∑ j ∈ Finset.range σ.length, moveCost (S' j) (S' (j + 1)))
          + moveCost (S' σ.length) X
        ≤ (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) X := by sorry

end KServer
