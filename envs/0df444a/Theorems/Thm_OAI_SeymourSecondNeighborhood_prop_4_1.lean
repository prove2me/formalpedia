-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_prop_4_1
-- name    : OAI.SeymourSecondNeighborhood.prop_4_1
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-13T20:28:25.942394+00:00
-- url     : https://prove2.me/theorems/4b10b006-8361-4128-a8de-75ca976c22cf
-- title:
--   Proposition 4.1 (extremal contradiction): no nonempty oriented graph with positive indegrees satisfies $|U|+|F^2(U)|<2|F(U)|$ for every nonempty proper $U$
-- statement:
--   Let $G$ be a nonempty finite oriented graph on $X$ (a loopless asymmetric relation) in which every vertex has an in-neighbor, and let $F(U)=\{y:\exists x\in U,\ x\to y\}$ be its one-step image operator. Then $G$ is not a strict expander: it is impossible that
--   $$|U|+|F^2(U)|<2\,|F(U)|\qquad\text{for every }\emptyset\neq U\subsetneq X.$$
--   This is Proposition 4.1 of the manuscript and the heart of its argument. The proof there is an extremal argument on pairs of families $P,Q\subseteq X\times X$: with the coordinate image operators $F_1S=\{(i,j):(p,j)\in S,\ p\to i\}$ and $F_2S=\{(i,j):(i,s)\in S,\ s\to j\}$, call $P,Q$ compatible if $F_1P\cap F_2Q=\emptyset$, and choose a compatible pair containing the diagonal that maximizes $|P|+|Q|+d$, where $d$ is the number of points of $X\times X$ outside $F_1P\cup F_2Q$. Summing the strict expansion inequality over the columns of $P$ and the rows of $Q$ (nonempty proper sets, by positive indegrees and compatibility) gives $|P|+|F_1^2P|<2|F_1P|$ and $|Q|+|F_2^2Q|<2|F_2Q|$; the complements $R=(X\times X)\setminus F_2^2Q$ and $C=(X\times X)\setminus F_1^2P$ then satisfy $|R|+|C|>|P|+|Q|+2d$, contain the diagonal with its members conflict-free, and the set $H$ of their conflicts has at most $d$ points. The pruning lemma (`Pruning.lemma_3_1`) restores compatibility while deleting at most $d+d'$ members, where $d'$ counts the points left uncovered afterwards, so the pruned pair has objective $>|P|+|Q|+d$, contradicting maximality. Together with Lemmas 2.2 and 2.3 this proposition implies Seymour's second-neighborhood conjecture (`exists_goodVertex`).
-- source:
--   Statement extracted from OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem prop_4_1 [Nonempty V] (r : V → V → Prop) (hr : IsOriented r) (hin : PosIndeg r) :
    ¬ StrictExpander r := by
  sorry

end OAI.SeymourSecondNeighborhood
