-- Prove2me | Theorems.Thm_Menger27_Graphs_glue_paths
-- name    : Menger27.Graphs.glue_paths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:19:13.503828+00:00
-- url     : https://prove2.me/theorems/99db89f9-cff9-4202-be25-756e7a6b4350
-- title:
--   p. 102, proof of Satz δ — n − p paths on the P-side and n − q paths on the Q-side of an n-point separator give n disjoint P–Q paths
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. Let $S \subseteq V$ be a set of exactly $n$ vertices separating $P$ and $Q$ in $G$, with $p = |S \cap P|$ and $q = |S \cap Q|$. Let $K_1$ and $K_2$ be the sides of $S$ towards $P$ and towards $Q$. Suppose that
--
--   1. $K_1$ contains $n - p$ pairwise disjoint paths from $P - S\cdot P$ to $S - S\cdot P$, and
--   2. $K_2$ contains $n - q$ pairwise disjoint paths from $Q - S\cdot Q$ to $S - S\cdot Q$.
--
--   Then $G$ contains $n$ pairwise disjoint paths from $P$ to $Q$.
--
--   Menger writes: "Ebenso enthält K₂, wenn die Menge S.Q etwa aus genau q Punkten besteht, n − q paarweise fremde Bögen zwischen Q − S.Q und S − S.Q. Diese n − p und n − q Bögen zusammen ergeben n paarweise fremde Teilbögen von K zwischen P und Q." This closes the induction step of Satz δ.
--
--   **Formalization Note.** Menger's arcs in $K_1$ lie in $K_1 \subseteq K' - S$ up to their end point in $S$; with $K_1$ as defined in this mission (no edges at the points of $S \cdot P$), a family of $n - p$ disjoint paths from $P - S$ to $S - P$ ends at every point of $S - P$ and meets $S$ only at its end points. The theorem is stated for any graph $G$ and any $n$-vertex separating set; $G$ is not assumed $n$-point connected. The subtractions $n - p$ and $n - q$ are exact because $p, q \le |S| = n$.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 102, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem glue_paths {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card))
    (hQ : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (n - (S ∩ Q).card)) :
    HasDisjointPaths G P Q n := by sorry

end Menger27.Graphs
