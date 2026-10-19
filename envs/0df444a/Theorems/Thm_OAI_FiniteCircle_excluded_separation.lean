-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_separation
-- name    : OAI.FiniteCircle.excluded_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:40:13.527027+00:00
-- url     : https://prove2.me/theorems/2294df2a-0d5b-469a-8a56-97461245cec8
-- title:
--   Separation of hierarchical excluded-sum words under a global phase shift
-- statement:
--   **Parameters.** Let $h\ge4$ and $R\ge1$ be natural numbers, let $M\ge1$ be even, and let $p(l,k)$ ($l\in\mathbb{N}$, $0\le k<h$) be positive integers dividing $M$. Put $P_l=\prod_{k<h}p(l,k)$, write $\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}$ and let $\iota_{l,k}:\mathbb{Z}_{p(l,k)}\to\mathbb{Z}_M$ be $a\mapsto(M/p(l,k))\,a$.
--
--   **States and shifts.** A level-$0$ state is a phase $v\in\mathbb{Z}_M$, and a level-$(l+1)$ state is a family $v=(v_0,\dots,v_{h-1})$ of level-$l$ states; for $\theta\in\mathbb{Z}_M$, $v+\theta$ is the state obtained by adding $\theta$ to every leaf phase.
--
--   **Words.** $X_0(v)$ is the half-circle word with position labels: its $i$-th letter ($0\le i<M$) is the pair $(i,\beta_v(i))$, where $\beta_v(i)=1$ iff the representative of $i-v$ in $\{0,\dots,M-1\}$ is less than $M/2$. For a row index $s\in\mathbb{N}$ and $0\le i<h$ put
--
--   $$
--   \chi_{l+1,s}(i)=\sum_{j<h,\ j\ne i}\frac{M}{p(l+1,j)}\,\bigl(s\bmod p(l+1,j)\bigr)\in\mathbb{Z}_M .
--   $$
--
--   The $s$-th row of a level-$(l+1)$ state $v$ is the concatenation over $i=0,\dots,h-1$ of the words $X_l(v_i+\chi_{l+1,s}(i))$ with every letter paired with $i$, and $X_{l+1}(v)$ is the concatenation of the rows $s=0,\dots,RP_{l+1}-1$. All level-$l$ words have length $L'_l$, where $L'_0=M$ and $L'_{l+1}=RP_{l+1}\,h\,L'_l$.
--
--   **Costs.** Let $e_0(x)=\|x\|/M$, with $\|x\|$ the circular distance from $x$ to $0$ in $\mathbb{Z}_M$, and
--
--   $$
--   e_{l+1}(x)=\min_{z\in\prod_{k<h}\mathbb{Z}_{p(l+1,k)}}\ \frac1h\sum_{i<h}e_l\Bigl(x+\sum_{j<h,\ j\ne i}\iota_{l+1,j}(z_j)\Bigr).
--   $$
--
--   For words $x,y$ let $\mathrm{def}(x,y)=|x|-\mathrm{lcs}(x,y)$, where $\mathrm{lcs}(x,y)$ is the length of a longest common subsequence.
--
--   **Theorem.** For every level $l$, every level-$l$ state $v$ and every $\theta\in\mathbb{Z}_M$,
--
--   $$
--   \frac{1}{2^l\cdot4}\,L'_l\,e_l(\theta)\le\mathrm{def}\bigl(X_l(v),\,X_l(v+\theta)\bigr).
--   $$
--
--   This is the excluded-sum analogue of the separation inequality for mask words: it converts the iterated-average cost $e_l(\theta)$ into a lower bound on the deficit, and hence on the edit distance, between a word of the excluded-sum family and its global phase shift. Combined with lower bounds on the costs $e_l$, it supplies deficit lower bounds for the excluded-sum word family, which enter the lower bound on the distortion of embedding edit distance into $\ell_1$.
--
--   **Formalization Note** Here $h$ is the number of coordinates per level. The hypothesis `ht : ∀ l, 4 ≤ (excludedTags h l).length` is equivalent to $h\ge4$, because `excludedTags h l` is the list $0,1,\dots,h-1$; the separate hypothesis $0<h$ is then redundant. The objects are `ExcludedState h M l`, `shiftExcludedState h M l`, `excludedWord h p R M l`, `excludedLength h p R M l` and `excludedCost h p M hd hn l`; evenness is `M = 2*(M/2)` and the deficit is cast to the reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean#L283-L386

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

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.excluded_separation {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (he : M = 2*(M/2)) (hh : 0 < h) (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (ht : ∀ l, 4 ≤ (excludedTags h l).length)
    (l : ℕ) (v : ExcludedState h M l) (θ : ZMod M) :
    (1/((2:ℝ)^l*4))*(excludedLength h p R M l)*excludedCost h p M hd hn l θ ≤
      (deficit (excludedWord h p R M l v)
        (excludedWord h p R M l (shiftExcludedState h M l v θ)) : ℝ) := by sorry
