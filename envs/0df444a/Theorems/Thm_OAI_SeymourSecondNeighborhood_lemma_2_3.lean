-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_lemma_2_3
-- name    : OAI.SeymourSecondNeighborhood.lemma_2_3
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T20:29:16.546975+00:00
-- url     : https://prove2.me/theorems/eb820c8b-d090-4430-b09a-3e639f43f534
-- title:
--   Lemma 2.3 (transitive-tournament blow-up): $D[T_m]$ with $m>|V(D)|$ turns the subset deficit into strict expansion $|U|+|F^2(U)|<2|F(U)|$ for every nonempty proper $U$
-- statement:
--   Let $D$ be an oriented graph on a finite vertex set $V$ with $n=|V|$, in which every vertex has an in-neighbor and which satisfies the subset deficit $|F^2(S)\setminus F(S)|<|F(S)\setminus S|$ for every nonempty proper $S\subseteq V$. Let $m>n$ and let $G=D[T_m]$ be the graph on $V\times\{0,\dots,m-1\}$ obtained by replacing each vertex by a transitive tournament on $m$ labels (arcs from smaller to larger labels) and, for every arc $v\to w$ of $D$, putting all arcs from the block at $v$ to the block at $w$ (`blowup r m`). Then $G$ is an oriented graph, every vertex of $G$ has an in-neighbor, and
--   $$|U|+|F_G^2(U)|<2\,|F_G(U)|\qquad\text{for every }\emptyset\neq U\subsetneq V(G)$$
--   (`StrictExpander`), where $F_G$ is the one-step image operator of $G$. This is Lemma 2.3 of the manuscript. In the proof, for a nonempty proper $U$ with label sets $T_v$ in the blocks and support $S=\{v:T_v\neq\emptyset\}$, one has $|F_G(U)|=m|F(S)|+\sum_{v\in S\setminus F(S)}|f(T_v)|$ and $|F_G^2(U)|\le m|F(S)\cup F^2(S)|+\sum_{v\in S\setminus(F(S)\cup F^2(S))}|f^2(T_v)|$, where $f$ is the image operator of the transitive tournament, which satisfies $|T|-2|f(T)|+|f^2(T)|\le1$; summing gives $|U|-2|F_G(U)|+|F_G^2(U)|\le m\,(|F^2(S)\setminus F(S)|-|F(S)\setminus S|)+n\le -m+n<0$ when $S\neq V$, and $|U|-|V(G)|<0$ when $S=V$. The same product construction appears in Brantner, Brockman, Kay and Snively, Involve 2 (2009), Theorem 4.3.
-- source:
--   Statement extracted from OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lemma_2_3 (r : V → V → Prop) (hr : IsOriented r) (hin : PosIndeg r)
    (hdef : SubsetDeficit r) (m : ℕ) (hm : Fintype.card V < m) :
    IsOriented (blowup r m) ∧ PosIndeg (blowup r m) ∧ StrictExpander (blowup r m) := by
  sorry

end OAI.SeymourSecondNeighborhood
