-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_lemma_2_2
-- name    : OAI.SeymourSecondNeighborhood.lemma_2_2
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T20:27:34.121559+00:00
-- url     : https://prove2.me/theorems/077c2be5-5e89-4eb3-a64c-a5b23b9aa146
-- title:
--   Lemma 2.2 (subset deficit): a minimal counterexample has positive indegrees and satisfies $|F^2(S)\setminus F(S)|<|F(S)\setminus S|$ for every nonempty proper $S$
-- statement:
--   Let $D$ be a finite nonempty oriented graph on $V$ (a loopless asymmetric relation $r$) in which every vertex $v$ is bad, i.e. $|N_1^+(v)|>|N_2^+(v)|$, where $N_1^+(v)$ is the out-neighborhood and $N_2^+(v)$ the set of vertices at directed distance exactly two. Assume $D$ is minimal in the following two senses: every proper subrelation $r'\subsetneq r$ (obtained by deleting at least one arc) has a good vertex, and every nonempty proper induced subgraph $D[W]$, $\emptyset\neq W\subsetneq V$, has a good vertex. Write $F(S)=\{y:\exists x\in S,\ x\to y\}$ for the one-step image (`fwd`). Then every vertex of $D$ has an in-neighbor, and
--   $$|F^2(S)\setminus F(S)|<|F(S)\setminus S|\qquad\text{for every }\emptyset\neq S\subsetneq V$$
--   (`SubsetDeficit`). This is Lemma 2.2 of the manuscript, which adapts the arc-deletion argument of Seacrest's Lemma 4 (arXiv:1808.06293): for $S$ fixed, put $I=F(S)\cap S$, $E=F(S)\setminus S$ and $g(T)=|F(T)\setminus(I\cup T)|$ for $T\subseteq E$; deleting the arcs from $S$ to $E\setminus T$ and using arc-minimality produces a nonempty $Q\subseteq E\setminus T$ with $g(T\cup Q)-g(T)<|Q|$, and iterating from $T=\emptyset$ to $T=E$ gives $g(E)<|E|$. The two minimality hypotheses are exactly what a counterexample of minimum order and then minimum number of arcs provides (the induced-subgraph hypothesis follows from the main theorem for smaller orders).
-- source:
--   Statement extracted from OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lemma_2_2 [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r a b) v) :
    PosIndeg r ∧ SubsetDeficit r := by
  sorry

end OAI.SeymourSecondNeighborhood
