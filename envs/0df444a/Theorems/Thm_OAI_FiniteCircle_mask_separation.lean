-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_separation
-- name    : OAI.FiniteCircle.mask_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:37:37.296618+00:00
-- url     : https://prove2.me/theorems/776bc753-71f4-477d-8110-39ed1958985a
-- title:
--   Separation of hierarchical mask words under a global phase shift
-- statement:
--   **Parameters.** Let $h\ge1$ and $R\ge1$ be natural numbers, let $M\ge1$ be even, and let $p(l,k)$ ($l\in\mathbb{N}$, $0\le k<h$) be positive integers with $p(l,k)\mid M$ for all $l,k$ and $t_l:=\sum_{k<h}p(l,k)\ge4$ for every $l$. Put $P_l=\prod_{k<h}p(l,k)$, write $\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}$, and let $\iota_{l,k}:\mathbb{Z}_{p(l,k)}\to\mathbb{Z}_M$ be $a\mapsto (M/p(l,k))\,a$.
--
--   **Tags, states, shifts.** The level-$l$ tags are the pairs $j=(k,b)$ with $k<h$ and $b<p(l,k)$, listed lexicographically; there are $t_l$ of them. A level-$0$ state is a phase $v\in\mathbb{Z}_M$, and a level-$(l+1)$ state is a family $v=(v_j)_j$ of level-$l$ states indexed by the level-$(l+1)$ tags; thus a state is a tree of depth $l$ whose leaves carry phases. For $\theta\in\mathbb{Z}_M$, $v+\theta$ denotes the state obtained by adding $\theta$ to every leaf.
--
--   **Words.** For $v\in\mathbb{Z}_M$ let $W_0(v)=H_v\in\{0,1\}^M$ be the half-circle word, whose $i$-th letter is $1$ iff the representative of $i-v$ in $\{0,\dots,M-1\}$ is less than $M/2$. For $l\ge0$, a row index $a\in\mathbb{N}$ and a level-$(l+1)$ tag $j=(k,b)$ put
--
--   $$
--   \gamma_{l+1,a}(j)=\sum_{k'<h}\frac{M}{p(l+1,k')}\,\bigl(a\bmod p(l+1,k')\bigr)+b\,\frac{M}{p(l+1,k)}\,\bigl(a\bmod p(l+1,k)\bigr)\in\mathbb{Z}_M .
--   $$
--
--   The $a$-th row of a level-$(l+1)$ state $v$ is the concatenation, over the level-$(l+1)$ tags $j$ in order, of the words $W_l(v_j+\gamma_{l+1,a}(j))$ with every letter paired with its tag $j$; and $W_{l+1}(v)$ is the concatenation of the rows $a=0,1,\dots,RP_{l+1}-1$. Every level-$l$ word has the same length $L_l$, where $L_0=M$ and $L_{l+1}=RP_{l+1}\,t_{l+1}\,L_l$.
--
--   **Costs.** Let $c_0(x)=\|x\|/M$, where $\|x\|$ is the circular distance from $x$ to $0$ in $\mathbb{Z}_M$, and for $l\ge0$
--
--   $$
--   c_{l+1}(x)=\min_{z\in\prod_{k<h}\mathbb{Z}_{p(l+1,k)}}\ \frac{1}{t_{l+1}}\sum_{(k,b)}c_l\Bigl(x+\sum_{k'<h}\iota_{l+1,k'}(z_{k'})+b\,\iota_{l+1,k}(z_k)\Bigr),
--   $$
--
--   the sum running over the level-$(l+1)$ tags. For words $x,y$, $\mathrm{lcs}(x,y)$ is the maximal length of a common subsequence and $\mathrm{def}(x,y)=|x|-\mathrm{lcs}(x,y)$.
--
--   **Theorem.** For every level $l$, every level-$l$ state $v$ and every $\theta\in\mathbb{Z}_M$,
--
--   $$
--   \frac{1}{2^{l}\cdot 4}\,L_l\,c_l(\theta)\le\mathrm{def}\bigl(W_l(v),\,W_l(v+\theta)\bigr).
--   $$
--
--   The inequality turns the arithmetic quantity $c_l(\theta)$, an iterated minimum of averages of circle costs, into a lower bound on how far a mask word is, in the deficit sense, from its own global phase shift. Combined with lower bounds on the costs $c_l$ it produces pairs of mask words at large deficit (and hence large edit distance), which is the combinatorial input for lower bounds on the distortion of embedding edit distance into $\ell_1$.
--
--   **Formalization Note** States, shifts, words, lengths and costs are `MaskState h p M l`, `shiftMaskState`, `maskWord h p R M l`, `maskLength h p R M l` and `maskCost h p M hd hn l` (built with `PhaseCost.step` over `maskPhaseHom`); level-$(l+1)$ letters are pairs (tag, level-$l$ letter). Evenness is `M = 2*(M/2)`, and the tag-count hypothesis is stated as `4 ≤ (maskTags h p l).length` for every `l`, including $l=0$ where it is not used. The deficit is a natural number cast to the reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean#L240-L330

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.mask_separation {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (he : M = 2*(M/2)) (hh : 0 < h) (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (ht : ∀ l, 4 ≤ (maskTags h p l).length)
    (l : ℕ) (v : MaskState h p M l) (θ : ZMod M) :
    (1/((2:ℝ)^l*4))*(maskLength h p R M l)*maskCost h p M hd hn l θ ≤
      (deficit (maskWord h p R M l v)
        (maskWord h p R M l (shiftMaskState h p M l v θ)) : ℝ) := by sorry
