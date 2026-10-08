-- Prove2me | Theorems.Thm_Menger27_Graphs_side_npoint_connected
-- name    : Menger27.Graphs.side_npoint_connected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:19:16.734041+00:00
-- url     : https://prove2.me/theorems/66861a7b-4eb4-480d-9556-7181b0a0574b
-- title:
--   p. 102, proof of Satz δ — the side K₁ of an n-point separator S is (n − p)-point connected between P − S·P and S − S·P
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. Suppose $G$ is $n$-point connected between $P$ and $Q$, and let $S \subseteq V$ be a set of exactly $n$ vertices separating $P$ and $Q$ in $G$. Write $p = |S \cap P|$ and let $K_1$ be the side of $S$ towards $P$ (the components of $G - S$ that meet $P - S$, with their edges to $S - P$). Then $K_1$ is $(n - p)$-point connected between $P - S\cdot P$ and $S - S\cdot P$:
--   $$\forall\, T \subseteq V:\quad T \text{ separates } P - S \text{ and } S - P \text{ in } K_1 \ \Longrightarrow\ |T| \ge n - p .$$
--
--   Menger writes: "Wenn die Menge S.P etwa genau p Punkte enthält, dann ist K₁ zwischen P − S.P und S − S.P mindestens (n − p)-punktig zusammenhängend". Applying the induction hypothesis to $K_1$, which has smaller degree, gives $n - p$ disjoint paths from $P - S\cdot P$ to $S - S\cdot P$. The same statement with $P$ and $Q$ exchanged covers Menger's $K_2$.
--
--   **Formalization Note.** Since $S \cap P \subseteq S$ and $|S| = n$, $p \le n$, so the natural-number subtraction $n - p$ is exact. The side $K_1$ is the graph `sidePart G P S` of the definition file, built from $G$, $P$ and $S$.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 102, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem side_npoint_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n) :
    NPointConnected (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card) := by sorry

end Menger27.Graphs
