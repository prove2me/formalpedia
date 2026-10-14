-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_matching_bound
-- name    : OAI.SeymourSecondNeighborhood.Pruning.matching_bound
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-13T21:08:50.062862+00:00
-- url     : https://prove2.me/theorems/977fabb7-0d11-4afd-9795-8d66ba5a6a5d
-- title:
--   Matching bound for the augmented bipartite graph of two families of pairs: every matching of $\Gamma$ has at most $|Z|+|H|$ edges
-- statement:
--   Let $X$ be a finite set with an arbitrary binary relation $\to$, and let $R,C\subseteq X\times X$ be two families of ordered pairs. A left member $(p,j)\in R$ and a right member $(i,s)\in C$ *conflict* if $p\to i$ and $s\to j$; a conflict contributes the point $(i,j)$ to $Z$ and the point $(p,s)$ to $H$. A member $(p,j)\in R$ *covers* a point $(i,j)$ when $p\to i$, and a member $(i,s)\in C$ covers $(i,j)$ when $s\to j$. The *augmented bipartite graph* $\Gamma$ has left vertex set $R\sqcup Z_L$ and right vertex set $C\sqcup Z_R$, where $Z_L,Z_R$ are two copies of $Z$; its edges join each conflicting pair $(r,c)\in R\times C$, each $r\in R$ to the right copy of every point of $Z$ it covers, and each $c\in C$ to the left copy of every point of $Z$ it covers (there are no edges between $Z_L$ and $Z_R$). The statement is that
--   $$|M|\;\le\;|Z|+|H|\qquad\text{for every matching }M\text{ of }\Gamma,$$
--   where a matching is a set of edges with pairwise distinct left endpoints and pairwise distinct right endpoints. This is the core of Section 3 of the manuscript, where it is proved by a rank argument: with generic real coefficients $a_{xy},b_{xy}$ attached to the arrows, four matrices $L,N,A,B$ satisfy $NL=AB$, a maximum matching with the fewest member–member edges is encoded by $\operatorname{rank}L$, $\operatorname{rank}N$ and $\dim\ker A$, and Lemma 3.2 (`Pruning.lemma_3_2`, kernels at maximum support rank) controls the kernel vectors. Together with K\H{o}nig's theorem (`Pruning.konig`) it implies the pruning lemma `Pruning.lemma_3_1`, and hence (through `prop_4_1`, `lemma_2_2` and `lemma_2_3`) Seymour's second-neighborhood conjecture. The bound is tight: for the complete loopless relation on $n$ points with $R=C=X\times X$ one has $|M|=2n^2=|Z|+|H|$.
--
--   **Formalization note.** Both sides of $\Gamma$ are encoded as `(X × X) ⊕ (X × X)`: `Sum.inl` for members of $R$ (left) or $C$ (right), `Sum.inr` for the copies of points of $Z$. The hypothesis `hM` says every element of `M` is an edge of $\Gamma$ of one of the three kinds, and `h₁`, `h₂` say `M` is a matching.
-- source:
--   Statement extracted from Section 3 of OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf; Kőnig's theorem: D. Kőnig, Matematikai és Fizikai Lapok 38 (1931) 116–119.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Matching bound in the augmented bipartite graph `Γ`.** The graph `Γ` has left vertex set
`R ⊔ Z` (members of `R`, and left copies `Sum.inr z` of the points `z ∈ Z = pointsZ arrow R C`)
and right vertex set `C ⊔ Z` (members of `C`, and right copies of the points of `Z`), encoded as
`(X × X) ⊕ (X × X)` on both sides. Its edges are
* the conflict edges `(inl l, inl c)` with `l ∈ R`, `c ∈ C`, `Conflict arrow l c`;
* the left-cover edges `(inl l, inr z)` with `l ∈ R`, `z ∈ Z`, `CoversL arrow l z`;
* the right-cover edges `(inr z, inl c)` with `z ∈ Z`, `c ∈ C`, `CoversR arrow c z`.

Every matching `M` of `Γ` (a set of edges of `Γ` on which both projections are injective) has at
most `|Z| + |H|` edges, where `H = pointsH arrow R C`. -/
theorem matching_bound (arrow : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X))))
    (hM : ∀ e ∈ M,
      (∃ l ∈ R, ∃ c ∈ C, e = (Sum.inl l, Sum.inl c) ∧ Conflict arrow l c) ∨
      (∃ l ∈ R, ∃ z ∈ pointsZ arrow R C, e = (Sum.inl l, Sum.inr z) ∧ CoversL arrow l z) ∨
      (∃ z ∈ pointsZ arrow R C, ∃ c ∈ C, e = (Sum.inr z, Sum.inl c) ∧ CoversR arrow c z))
    (h₁ : Set.InjOn Prod.fst (M : Set (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X)))))
    (h₂ : Set.InjOn Prod.snd (M : Set (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X))))) :
    M.card ≤ (pointsZ arrow R C).card + (pointsH arrow R C).card := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
