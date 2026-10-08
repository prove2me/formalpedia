-- Prove2me | Theorems.Thm_Menger27_Graphs_satz_delta
-- name    : Menger27.Graphs.satz_delta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:09.923984+00:00
-- url     : https://prove2.me/theorems/96a80b0c-47b7-4601-9c3c-6d4457918d0a
-- title:
--   Satz δ (p. 101) — Menger's theorem: if no fewer than n vertices separate disjoint finite sets P and Q, then n disjoint paths join P to Q
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$, let $P, Q \subseteq V$ be disjoint sets of vertices, and let $n \ge 0$. Suppose that $G$ is $n$-point connected between $P$ and $Q$: every set $S \subseteq V$ such that every walk from a vertex of $P$ to a vertex of $Q$ passes through $S$ has at least $n$ elements. Then $G$ contains $n$ pairwise vertex-disjoint paths, each starting at a vertex of $P$ and ending at a vertex of $Q$:
--   $$\min\{\,|S| : S \text{ separates } P \text{ and } Q\,\} \ \ge\ n \quad\Longrightarrow\quad \exists\ \text{paths } W_1, \dots, W_n \text{ from } P \text{ to } Q \text{ with pairwise disjoint vertex sets.}$$
--
--   This is Satz δ of Menger's paper (p. 101), "Satz δ = Satz β für gewöhnlich eindimensionale Räume", where Satz β (p. 100) reads: "Ist K ein kompakter regulär eindimensionaler Raum, welcher zwischen den beiden endlichen Mengen P und Q n-punktig zusammenhängend ist, dann enthält K n paarweise fremde Bögen, von denen jeder einen Punkt von P und einen Punkt von Q verbindet." A *gewöhnlich eindimensionaler Raum* is a finite union of arcs any two of which meet at most in end points. In graph language this is Menger's theorem in its set form, the source of the max-flow/min-cut and Kőnig–Egerváry family of min–max theorems.
--
--   **Formalization Note.** The finite union of arcs is read as a finite simple graph (see the definition file `Menger27.Graphs.Separation`). The paths are disjoint including their end points, not merely internally disjoint, and separating sets may contain vertices of $P$ and $Q$. The disjointness of $P$ and $Q$ is part of Menger's definition of $n$-point connectedness ("zwischen den beiden fremden … Teilmengen") and is a hypothesis here. Since $P \cap Q = \emptyset$, every path of the conclusion has at least one edge, as Menger's arcs do; without the hypothesis a common vertex of $P$ and $Q$ would count as a path of length $0$, which is not an arc. Only the direction stated by Menger is formalized; the converse is not part of the paper.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101, Satz δ (with Satz β, p. 100, and the definition of gewöhnlich eindimensionale Räume, p. 101)

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem satz_delta {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    HasDisjointPaths G P Q n := by sorry

end Menger27.Graphs
