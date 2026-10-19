-- Prove2me | Theorems.Thm_OAI_FiniteCircle_tree_cheap_ed
-- name    : OAI.FiniteCircle.tree_cheap_ed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:53:33.57099+00:00
-- url     : https://prove2.me/theorems/20256738-00a3-43f9-9c92-2d151f379238
-- title:
--   Cheap translations change recursively concatenated tree words by edit distance at most $2lL_l/R$
-- statement:
--   This result bounds how much a recursively defined family of words changes, in edit distance, when its state is translated by an element of a recursively defined "cheap" subgroup.
--
--   **Setting.** Fix natural numbers $M$ and $R$ with $R>0$, write $\mathbb Z_M=\mathbb Z/M\mathbb Z$, and fix functions $P,L\colon\mathbb N\to\mathbb N$, written $l\mapsto P_l$, $l\mapsto L_l$. For every level $l\in\mathbb N$ let $J_l$ and $A_l$ be types and $Z_l$ an abelian group. The *leaves* of level $l$ are $\mathcal T_0=\{\ast\}$ and $\mathcal T_{l+1}=J_{l+1}\times\mathcal T_l$, so a leaf is a path $(j_l,j_{l-1},\dots,j_1)$ with $j_r\in J_r$. A *state* of level $l$ is a function $v\colon\mathcal T_l\to\mathbb Z_M$. For a state $v$ of level $l+1$ and $j\in J_{l+1}$ let $v(j,\cdot)$ be the state $i\mapsto v(j,i)$ of level $l$, and for $\vartheta\in\mathbb Z_M$ let $v+\vartheta$ be the state obtained by adding $\vartheta$ at every leaf. Suppose that for each $l$ we are given
--
--   - a list $\tau_l$ of elements of $J_{l+1}$, of length $|\tau_l|$;
--   - maps $\mathrm{tag}_l(j,\cdot)\colon A_l\to A_{l+1}$ for $j\in J_{l+1}$, applied to words letter by letter;
--   - a group homomorphism $\sigma_l\colon Z_l\to(\mathbb Z_M)^{J_l}$;
--   - phases $\gamma_l(a,j)\in\mathbb Z_M$ for $a\in\mathbb N$ and $j\in J_{l+1}$;
--   - a map $W_l$ sending each state of level $l$ to a finite word over $A_l$,
--
--   such that for all $l$ and all states $v$:
--
--   1. $|W_l(v)|=L_l$, and $L_{l+1}=R\,P_{l+1}\,|\tau_l|\,L_l$;
--   2. $W_{l+1}(v)$ is the concatenation, over $a=0,1,\dots,RP_{l+1}-1$ in increasing order and, for each $a$, over $j$ running through the list $\tau_l$, of the words $\mathrm{tag}_l\bigl(j,\,W_l(v(j,\cdot)+\gamma_l(a,j))\bigr)$;
--   3. for every $z\in Z_{l+1}$ there is a natural number $q<P_{l+1}$ with $\gamma_l(q+a,j)=\sigma_{l+1}(z)(j)+\gamma_l(a,j)$ for all $a\in\mathbb N$ and all $j\in J_{l+1}$.
--
--   The *cheap subgroups* $H_l\le(\mathbb Z_M)^{\mathcal T_l}$ are defined by $H_0=\{0\}$ and: $c\in H_{l+1}$ if and only if there are $c_j\in H_l$ (one for each $j\in J_{l+1}$) and $z\in Z_{l+1}$ such that $c(j,i)=c_j(i)+\sigma_{l+1}(z)(j)$ for all $j\in J_{l+1}$ and $i\in\mathcal T_l$.
--
--   **Statement.** Let $\operatorname{ed}$ denote edit distance (the least number of single-letter insertions, deletions and substitutions). For every level $l$, every state $v$ of level $l$ and every $c\in H_l$,
--
--   $$
--   R\cdot\operatorname{ed}\bigl(W_l(v),\,W_l(v+c)\bigr)\;\le\;2\,l\,L_l .
--   $$
--
--   Each level of the construction repeats a block of rows $RP_{l+1}$ times with phases $\gamma_l(a,\cdot)$, and condition 3 says that the top-level part $\sigma_{l+1}(z)$ of a cheap translation has the same effect as re-indexing the rows by a shift $q<P_{l+1}$. The theorem turns this into a quantitative estimate: a cheap translation moves a word of length $L_l$ by edit distance at most $2lL_l/R$, a small fraction of its length when $R$ is large. It is the generic cheap-direction estimate for the recursive circle words of the lower-bound construction (it is instantiated both for the mask words and for the excluded-residue words) and supplies the cheap-translation hypothesis of the Fourier-analytic distortion bound.
--
--   **Formalization Note** Leaves are `TreeLeaf J l` (`PUnit` at level 0 and `J (l+1) × TreeLeaf J l` above), the cheap subgroup $H_l$ is `treeCheap J Z σ l`, the concatenations are `List.flatMap` over `List.range (R*P (l+1))` and over the list `tags l`, and the inequality is between natural numbers. No finiteness of the types $J_l$ and no positivity of $M$ is assumed (for $M=0$, `ZMod 0` is $\mathbb Z$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Translations.lean#L122-L193

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.tree_cheap_ed (J Z A : ℕ → Type) [∀ l, AddCommGroup (Z l)]
    {M R : ℕ} (hR : 0 < R) (P L : ℕ → ℕ)
    (tags : ∀ l, List (J (l+1)))
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (σ : ∀ l, Z l →+ (J l → ZMod M))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hlen : ∀ l v, (W l v).length = L l)
    (hL : ∀ l, L (l+1) = (R*P (l+1))*((tags l).length*L l))
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (hCRT : ∀ l z, ∃ q : ℕ, q < P (l+1) ∧ ∀ a j, γ l (q+a) j = σ (l+1) z j+γ l a j)
    (l : ℕ) (v c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    R*editDistance (W l v) (W l (v+c)) ≤ 2*l*L l := by sorry
