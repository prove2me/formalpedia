-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_exists_rank_ultrafilter
-- name    : OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:38:12.690952+00:00
-- url     : https://prove2.me/theorems/a9a5b2a8-1799-4840-a1a4-b232e2316e4d
-- title:
--   An ultrafilter avoiding a subset ideal, containing every column, with each member almost below only finitely many columns
-- statement:
--   Let $\alpha$ and $\iota$ be arbitrary types. Let $\mathcal K$ be a *subset ideal* on $\alpha$: a family of subsets of $\alpha$, called $\mathcal K$-small, that contains $\emptyset$, is closed under subsets and under finite unions, and does not contain $\alpha$. Write $X\subseteq_{\mathcal K}Y$ if $X\setminus Y$ is $\mathcal K$-small. Let $(G_t)_{t\in\iota}$ be a family of subsets of $\alpha$ (the *columns*), and for finite sets $F,H\subseteq\iota$ let
--   $$\mathrm{Pat}(F,H)=\{x\in\alpha:\ x\in G_t\ \text{for all } t\in F,\ \ x\notin G_t\ \text{for all } t\in H\}.$$
--
--   **Theorem.** Assume that $\mathrm{Pat}(F,H)$ is not $\mathcal K$-small for all finite $F,H\subseteq\iota$ with $F\cap H=\emptyset$. Then there exists an ultrafilter $\mathcal U$ on $\alpha$ such that
--
--   1. no $\mathcal K$-small set belongs to $\mathcal U$;
--   2. $G_t\in\mathcal U$ for every $t\in\iota$;
--   3. for every $X\in\mathcal U$ the set of columns lying above $X$ modulo $\mathcal K$ is finite:
--   $$\#\{t\in\iota:\ X\setminus G_t \text{ is } \mathcal K\text{-small}\}<\infty .$$
--
--   In the counterexample this is applied on $D$ with the concrete density ideal and a continuum-indexed family of columns whose signed patterns are all non-small, and the ultrafilter is the starting point of the ordinal rank function: property 3 is what later allows a large set to be thinned to one of arbitrarily large rank. The argument uses only finite intersections, so no countable completeness of $\mathcal U$ and no regularity of the continuum is needed.
--
--   **Formalization Note** `SubsetIdeal α` bundles the predicate `small` with the axioms `empty`, `mono`, `union` and `proper` ($\alpha$ itself is not small). `K.ModSubset X Y` is `K.small (X \ Y)`, `columnPattern G F H` is $\mathrm{Pat}(F,H)$ for finsets `F H : Finset ι` with `Disjoint F H`, and `Ultrafilter α` is Mathlib's ultrafilter type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Ideals.lean#L107-L161

import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals

open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped symmDiff

theorem OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α)
    (hpattern : ∀ F H : Finset ι, Disjoint F H → ¬ K.small (columnPattern G F H)) :
    ∃ U : Ultrafilter α,
      (∀ N, K.small N → N ∉ U) ∧ (∀ t, G t ∈ U) ∧
      (∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite) := by sorry
