-- Prove2me | Theorems.Thm_Menger27_Graphs_exists_irreducible_part
-- name    : Menger27.Graphs.exists_irreducible_part
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:56.114915+00:00
-- url     : https://prove2.me/theorems/0b8fa034-1b97-4939-b1c1-ee15e497bb94
-- title:
--   p. 101, proof of Satz δ — an n-point connected graph contains an irreducibly n-point connected part
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. If $G$ is $n$-point connected between $P$ and $Q$, then $G$ has a part $K'$ (a spanning subgraph, $K' \le G$) that is *irreducibly* $n$-point connected between $P$ and $Q$: $K'$ is $n$-point connected between $P$ and $Q$, and no proper part of $K'$ is.
--
--   Menger writes: "Man kann aus K offenbar einen zwischen P und Q irreduzibel n-punktig zusammenhängenden Teil herausgreifen, d. h. einen zwischen P und Q n-punktig zusammenhängenden Teil K′, von dem kein echter Teil zwischen P und Q n-punktig zusammenhängend ist." The induction step of Satz δ is carried out on such a minimal part.
--
--   **Formalization Note.** Parts are spanning subgraphs of type `SimpleGraph V`, ordered by `≤`; a proper part is one with fewer edges. Menger calls the claim "offenbar".
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem exists_irreducible_part {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IrreduciblyNPointConnected K P Q n := by sorry

end Menger27.Graphs
