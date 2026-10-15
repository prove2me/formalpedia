-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_exists_maximal_wave
-- name    : OAI.InfiniteMatroidCounterexample.exists_maximal_wave
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:04:48.480062+00:00
-- url     : https://prove2.me/theorems/aeb9d278-c1ab-4f9e-a063-779ca358b5c5
-- title:
--   Every family of matroids admits a maximal wave
-- statement:
--   Let $\alpha$ and $\iota$ be types, let $(M_i)_{i\in\iota}$ be a family of matroids on $\alpha$ (each $M_i$ has its own ground set $E(M_i)\subseteq\alpha$ and closure operator $\operatorname{cl}_{M_i}$), and let $F\subseteq\alpha$. A *wave* for $(M,F)$ is a pair $W=\bigl(X,(W_i)_{i\in\iota}\bigr)$ consisting of a set $X\subseteq\alpha$ and a family of sets $W_i\subseteq\alpha$ such that
--
--   1. $X\subseteq F$;
--   2. $W_i\subseteq X$ for every $i\in\iota$;
--   3. $W_i\cap W_j=\emptyset$ whenever $i\neq j$;
--   4. $X\subseteq\operatorname{cl}_{M_i}(W_i)$ for every $i\in\iota$.
--
--   Thus $X$ contains, for each index $i$, a subset $W_i$ that spans $X$ in $M_i$, and these spanning sets are pairwise disjoint. Pairs are compared componentwise: $\bigl(X,(W_i)\bigr)\le\bigl(X',(W'_i)\bigr)$ means $X\subseteq X'$ and $W_i\subseteq W'_i$ for every $i$.
--
--   **Theorem.** There is a maximal wave: some wave $W$ for $(M,F)$ satisfies
--
--   $$
--   \forall\,W':\qquad W'\ \text{a wave for }(M,F)\ \text{ and }\ W\le W'\quad\Longrightarrow\quad W'\le W\quad(\text{hence }W'=W).
--   $$
--
--   No finiteness or cardinality assumption is made on $\alpha$, $\iota$ or the matroids, and $F$ is arbitrary. When all $M_i$ have ground set $F$, contracting the set $X$ of a maximal wave leaves a family $(M_i/X)_i$ on $F\setminus X$ whose only wave is the trivial one $(\emptyset,(\emptyset)_i)$; this is how a failure of the packing–covering property for a pair of matroids is turned into a counterexample to a covering statement about restrictions.
--
--   **Formalization Note** A wave is a term `W : Set α × (ι → Set α)` with `Wave M F W`, ordered by the product order, and `Maximal (Wave M F) W` is Mathlib's notion of maximality: `W` is a wave and every wave `W'` with `W ≤ W'` satisfies `W' ≤ W`. Closures are Mathlib's `Matroid.closure`, which is defined for all subsets of `α` and always lies in the ground set, so condition 4 forces $X\subseteq E(M_i)$ for each $i$; no relation between $F$ and the ground sets is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Waves.lean#L14-L44

import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves

open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid

theorem OAI.InfiniteMatroidCounterexample.exists_maximal_wave {α ι : Type*} (M : ι → Matroid α) (F : Set α) :
    ∃ W, Maximal (Wave M F) W := by sorry
