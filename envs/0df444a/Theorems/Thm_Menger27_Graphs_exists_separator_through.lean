-- Prove2me | Theorems.Thm_Menger27_Graphs_exists_separator_through
-- name    : Menger27.Graphs.exists_separator_through
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:18:39.270291+00:00
-- url     : https://prove2.me/theorems/6d62cd77-d3f3-458b-a38f-814585bee9b9
-- title:
--   p. 102, proof of Satz δ — through a vertex s outside P ∪ Q passes an n-point set separating P and Q
-- statement:
--   Let $K'$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. Suppose $K'$ is irreducibly $n$-point connected between $P$ and $Q$ and has more than $n$ edges, and let $s \notin P \cup Q$ be a vertex lying on an edge $st$ of $K'$. Then there is a set $S$ of exactly $n$ vertices, containing $s$, that separates $P$ and $Q$ in $K'$:
--   $$\exists\, S \subseteq V:\quad s \in S,\quad |S| = n,\quad S \text{ separates } P \text{ and } Q \text{ in } K' .$$
--
--   Menger writes: "In K′ − s sind n − 1 Punkte und daher auch n − 1 punktförmige Stücke s₂, s₃ … sₙ enthalten, so dass P und Q durch die Menge S = {s, s₂, … sₙ} getrennt sind". The separating set $S$ splits $K'$ into a side of $P$ and a side of $Q$, each of smaller degree.
--
--   **Formalization Note.** The page's "n − 1 points in K′ − s, so that P and Q are separated by S = {s, s₂, …, sₙ}" is rendered as the existence of a separating set of $n$ vertices containing $s$ (its other $n - 1$ elements are then vertices different from $s$). Menger's further gloss, that $K' - S$ splits into two disjoint closed parts containing $P - S\cdot P$ and $Q - S\cdot Q$, is the definition of separation and is contained in the conclusion.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 102, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem exists_separator_through {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card)
    (s : V) (hsP : s ∉ P) (hsQ : s ∉ Q) (t : V) (hst : K.Adj s t) :
    ∃ S : Finset V, s ∈ S ∧ S.card = n ∧ Separates K P Q S := by sorry

end Menger27.Graphs
