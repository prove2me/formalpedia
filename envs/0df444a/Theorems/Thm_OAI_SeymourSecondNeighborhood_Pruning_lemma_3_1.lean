-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1
-- name    : OAI.SeymourSecondNeighborhood.Pruning.lemma_3_1
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-13T20:29:49.119354+00:00
-- url     : https://prove2.me/theorems/ece226be-22b4-4711-bd31-f47df78d3606
-- title:
--   Lemma 3.1 (pruning two families of pairs): conflicts can be removed by deleting at most $|H|$ plus the number of uncovered points of $Z$ members
-- statement:
--   Let $X$ be a finite set with an arbitrary binary relation $\to$ (no orientation or irreflexivity is assumed), and let $R,C\subseteq X\times X$ be two families of ordered pairs, regarded as separate copies even where they agree. A left member $(p,j)\in R$ and a right member $(i,s)\in C$ *conflict* if $p\to i$ and $s\to j$. Let
--   $$Z=\{(i,j): \text{some }(p,j)\in R\text{ conflicts with some }(i,s)\in C\},\qquad H=\{(p,s): \text{some }(p,j)\in R\text{ conflicts with some }(i,s)\in C\}.$$
--   A point $(i,j)$ is *covered* by a member $(p,j)\in R$ when $p\to i$, and by a member $(i,s)\in C$ when $s\to j$. Then there are subfamilies $R'\subseteq R$ and $C'\subseteq C$ with no conflicts between them, such that every member of $R$ (resp. $C$) that conflicts with no member of $C$ (resp. $R$) is retained, and
--   $$|R\setminus R'|+|C\setminus C'|\;\le\;|H|+\bigl|\{z\in Z: z\text{ is covered by no member of }R'\cup C'\}\bigr|.$$
--   This is Lemma 3.1 of the manuscript, its main new ingredient. The proof there builds a bipartite graph on $R\sqcup Z_L$ and $C\sqcup Z_R$ (conflicting members adjacent; each member adjacent to the opposite copy of every point of $Z$ it covers), shows by a rank argument with generically chosen real coefficients (Lemma 3.2, `lemma_3_2`) that a maximum matching has at most $|Z|+|H|$ edges, and takes a K\H{o}nig vertex cover of that size; deleting its original members gives the pruning. The statement is purely about finite relations and families of pairs; in the application (`prop_4_1`) its two cost terms are bounded by the numbers of uncovered points before and after pruning.
-- source:
--   Statement extracted from OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem lemma_3_1 (arrow : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' ⊆ R, ∃ C' ⊆ C,
      (∀ l ∈ R', ∀ c ∈ C', ¬ Conflict arrow l c) ∧
      (∀ l ∈ R, (∀ c ∈ C, ¬ Conflict arrow l c) → l ∈ R') ∧
      (∀ c ∈ C, (∀ l ∈ R, ¬ Conflict arrow l c) → c ∈ C') ∧
      (R \ R').card + (C \ C').card
        ≤ (pointsH arrow R C).card + (uncovered arrow R C R' C').card := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
