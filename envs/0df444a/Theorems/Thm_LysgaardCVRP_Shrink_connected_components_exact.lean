-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_connected_components_exact
-- name    : LysgaardCVRP.Shrink.connected_components_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:12:28.085237+00:00
-- url     : https://prove2.me/theorems/45556d15-d52d-4929-a674-a0b12c1e3467
-- title:
--   The connected components heuristic finds a violated RCI at integer points
-- statement:
--   Let $Q > 0$ and let the customers have integer demands $0 < q_i \le Q$. Let $x$ be an integer point of the two-index formulation's LP relaxation:
--
--   1. $x_{ij} \in \{0, 1\}$ for distinct customers $i, j$;
--   2. $x_{0j} \in \{0, 1, 2\}$ for every customer $j$;
--   3. $x(\delta(\{i\})) = 2$ for every customer $i$.
--
--   Let $S_1, \dots, S_p$ be the connected components of the support graph $G^*_c$ on the customers, and let $U$ be the union of those components that have no edge of positive weight to the depot. If some rounded capacity inequality $x(\delta(T)) \ge 2k(T)$, with $T$ a customer set and $|T| \ge 2$, is violated, then it is violated for one of the checked sets: some $S_i$, some $V_c \setminus S_i$, or $U$ (each with at least two customers).
--
--   In words: the first separation heuristic of the algorithm, which checks exactly these sets, is exact when the LP solution is integral.
--
--   **Formalization Note** A checked set counts as a violated RCI when it has at least two customers and $2k(\cdot) - x(\delta(\cdot)) > 0$. $V_c$ is the set of all non-depot vertices.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), §2.1, first separation heuristic

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_LysgaardCVRP_Shrink_violation
import Definitions.Def_LysgaardCVRP_Shrink_customerComponent

namespace LysgaardCVRP.Shrink

/-- The connected components heuristic is exact at integer points, Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), §2.1, p. 426 (PDF p. 4)
(unnumbered): "First we compute the connected components $S_1, \dots, S_p$ of $G^*_c$. Then, for
every $i = 1, \dots, p$ we check the RCI for $S_i$ as well as for $V_c \setminus S_i$. Finally we
check the RCI for the union of those components which are not connected to the depot in $G^*$. We
note that this heuristic with certainty finds a violated RCI (if one exists) if $x^*$ is integer."

Let $x$ be an integer point of the LP relaxation: $x_{ij} \in \{0,1\}$ between distinct customers
(3), $x_{0j} \in \{0,1,2\}$ (4), and $x(\delta(\{i\})) = 2$ for every customer (1). If some RCI
$x(\delta(T)) \ge 2k(T)$ ($T$ a customer set, $|T| \ge 2$) is violated, then a violated RCI is found
among the sets $S_i$, $V_c \setminus S_i$, and the union of the components of $G^*_c$ that have no
edge of positive weight to the depot.

**Formalization Note.** Standing hypotheses $Q > 0$ and integer demands $0 < q_i \le Q$. A checked
set yields a violated RCI when it is a customer set with at least two elements and positive
violation $2k(\cdot) - x(\delta(\cdot))$. $V_c$ is `Finset.univ.erase 0`; $S_i$ is
`customerComponent x i` for a customer `i`. Values of `x` on diagonal pairs `s(i, i)` are
unconstrained and play no role. -/
theorem connected_components_exact {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ)
    (hx_cust : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j → x s(i, j) = 0 ∨ x s(i, j) = 1)
    (hx_depot : ∀ j : Fin (n + 1), j ≠ 0 →
      x s(0, j) = 0 ∨ x s(0, j) = 1 ∨ x s(0, j) = 2)
    (hdeg : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 2)
    (hviol : ∃ T : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ T ∧ 2 ≤ T.card ∧
      0 < violation x (roundedCapacityBound q Q) T) :
    (∃ i : Fin (n + 1), i ≠ 0 ∧
      ((2 ≤ (customerComponent x i).card ∧
          0 < violation x (roundedCapacityBound q Q) (customerComponent x i)) ∨
        (2 ≤ (Finset.univ.erase 0 \ customerComponent x i).card ∧
          0 < violation x (roundedCapacityBound q Q) (Finset.univ.erase 0 \ customerComponent x i)))) ∨
    (2 ≤ (detachedUnion x).card ∧ 0 < violation x (roundedCapacityBound q Q) (detachedUnion x)) := by sorry

end LysgaardCVRP.Shrink
