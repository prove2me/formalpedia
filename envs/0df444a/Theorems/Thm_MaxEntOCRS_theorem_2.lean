-- Prove2me | Theorems.Thm_MaxEntOCRS_theorem_2
-- name    : MaxEntOCRS.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:12.562149+00:00
-- url     : https://prove2.me/theorems/35378270-1a41-4fd1-b441-5b4788d7fae6
-- title:
--   Theorem 2 — occupancy $\le \alpha$ forces joint vacancy $\ge \alpha$; equality on the four-cycle
-- statement:
--   Let $\mu$ be the monomer–dimer measure of a finite loopless multigraph with nonnegative activities in which every vertex is covered with probability at most $\alpha = (\sqrt3-1)/2$. Then for every pair of distinct vertices $u, v$,
--   $$
--   \Pr_\mu(u \text{ and } v \text{ are both uncovered}) \ge \alpha .
--   $$
--   Equality holds for the four-cycle $u, y_1, v, y_2$ with all activities equal to $\alpha$ and $\{u, v\}$ a diagonal: there every vertex is covered with probability exactly $\alpha$, and each diagonal pair is uncovered with probability exactly $\alpha$.
--
--   The union bound gives only $1 - 2\alpha$, and the uncovered events of $u$ and $v$ can be negatively correlated in non-bipartite graphs. Theorem 2 is the core of Theorem 1.
--
--   Differences from the source:
--   - reading: Equality holds for the four-cycle with all activities equal to α and {u, v} a diagonal → on that four-cycle every vertex is covered with probability exactly α (the hypothesis holds) and both diagonals are uncovered with probability exactly α; reason: the equality case includes the hypothesis being met, as computed in A.8; 'a diagonal' covers both diagonals
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Theorem 2, p.2 (proof pp.5–8; A.7–A.8, pp.14–15)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_bothUncoveredProb
import Definitions.Def_MaxEntOCRS_fourCycle

namespace MaxEntOCRS

/-- Theorem 2 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.2; proof pp.7–8, A.7–A.8, pp.14–15). Let `μ` be a monomer–dimer measure
on a finite loopless multigraph in which every vertex is covered with probability at most `α`.
Then for every pair of distinct vertices `u, v`, `Pr_μ(u and v are both uncovered) ≥ α`.
Equality holds for the four-cycle with all activities equal to `α` and `{u, v}` a diagonal
(there every vertex is covered with probability exactly `α`, A.8). -/
theorem theorem_2 :
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ), (∀ e, 0 ≤ t e) →
        (∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) →
        ∀ u v : V, u ≠ v → alpha ≤ bothUncoveredProb G (monomerDimer G t) u v) ∧
      (∀ z : Fin 4, coverProb fourCycle (monomerDimer fourCycle (fun _ => alpha)) z = alpha) ∧
      bothUncoveredProb fourCycle (monomerDimer fourCycle (fun _ => alpha)) 0 2 = alpha ∧
      bothUncoveredProb fourCycle (monomerDimer fourCycle (fun _ => alpha)) 1 3 = alpha := by sorry

end MaxEntOCRS
