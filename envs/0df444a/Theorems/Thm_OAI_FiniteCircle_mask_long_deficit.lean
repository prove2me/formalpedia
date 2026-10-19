-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_long_deficit
-- name    : OAI.FiniteCircle.mask_long_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:44:33.024992+00:00
-- url     : https://prove2.me/theorems/6eb61e98-ad91-4435-86aa-4ad0949255ae
-- title:
--   A half-turn shift of all phases forces deficit at least $n^{-3n^4}$ times the length of a mask circle word
-- statement:
--   Let $n\ge10^6$ be an integer such that $n^4$ is even (equivalently, $n$ is even), and put $h=n^4$. Let $(p_{l,k})_{l,k\in\mathbb{N}}$ be a *standing prime array* for $h$: for $1\le l\le h$ and $0\le k<h$ the numbers $p_{l,k}$ are primes with $h^3<p_{l,k}\le2h^3$, these $h^2$ primes are pairwise distinct, and $p_{l,k}=1$ for every other pair $(l,k)$. Put $P_l=\prod_{k<h}p_{l,k}$, let $M=2\prod_{l=1}^{h}P_l$ (so every $p_{l,k}$ divides $M$ and $M$ is even), and fix an integer $R\ge1$. For words $x,y$ let $\operatorname{lcs}(x,y)$ be the length of a longest common subsequence and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$ the deficit.
--
--   *Mask circle words.* For $1\le l\le h$ the tags of level $l$ are the pairs $j=(k,b)$ with $0\le k<h$ and $0\le b<p_{l,k}$, listed lexicographically; there are $t_l=\sum_{k<h}p_{l,k}$ of them. A state of depth $0$ is a phase $v\in\mathbb{Z}/M$, and a state $v$ of depth $l\ge1$ assigns to each tag $j$ of level $l$ a state $v_j$ of depth $l-1$ (a rooted tree with phases at its leaves). For $\theta\in\mathbb{Z}/M$, $v+\theta$ denotes the state obtained by adding $\theta$ to every leaf phase. The word $W_l(v)$ is defined recursively:
--
--   1. $W_0(v)=w_0w_1\cdots w_{M-1}$ is the binary word with $w_b=1$ if and only if the residue of $b-v$ in $\{0,\dots,M-1\}$ is less than $M/2$;
--   2. for $l\ge1$, $W_l(v)$ is the concatenation, over $a=0,1,\dots,RP_l-1$ and, for each $a$, over the tags $j=(k,b)$ of level $l$ in order, of the word $W_{l-1}\big(v_j+\gamma_l(a,j)\big)$ with every letter labelled by $j$, where
--
--   $$
--   \gamma_l\big(a,(k,b)\big)=\sum_{k'<h}\frac{M}{p_{l,k'}}\,(a\bmod p_{l,k'})+b\,\frac{M}{p_{l,k}}\,(a\bmod p_{l,k})\ \in\mathbb{Z}/M .
--   $$
--
--   Every word $W_l(v)$ has the same length $L_l$, where $L_0=M$ and $L_l=R\,P_l\,t_l\,L_{l-1}$.
--
--   **Theorem.** For every state $v$ of depth $h$,
--
--   $$
--   \frac{L_h}{n^{3n^4}}\le\operatorname{def}\Big(W_h(v),\,W_h\big(v+\tfrac M2\big)\Big).
--   $$
--
--   Thus shifting every phase of a mask circle word by half a turn destroys, in the longest-common-subsequence sense, at least a fraction $n^{-3n^4}$ of the word. This is the long-move separation used in the lower bound on the $\ell^1$ distortion of the family of encoded mask words.
--
--   **Formalization Note** The prime array is `StandingPrimes (n^4) p`, $M$ is `circleSize (n^4) p`, $W_l$ is `maskWord (n^4) p R M l`, $L_l$ is `maskLength (n^4) p R M l`, the shift is `shiftMaskState`, $\gamma_l$ is `maskGamma` (with the exact natural-number quotients $M/p$), and $\operatorname{def}$ is `deficit`, which uses truncated subtraction (harmless since $\operatorname{lcs}(x,y)\le|x|$). The evenness hypothesis is stated as $n^4=2\lfloor n^4/2\rfloor$, and the half turn is the class of the natural number $\lfloor M/2\rfloor=M/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/DeficitLower.lean#L40-L77

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

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.mask_long_deficit {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2))
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {R : ℕ} (hR : 0<R)
    (v : MaskState (n^4) p (circleSize (n^4) p) (n^4)) :
    (maskLength (n^4) p R (circleSize (n^4) p) (n^4):ℝ)/(n:ℝ)^(3*n^4) ≤
      (deficit (maskWord (n^4) p R (circleSize (n^4) p) (n^4) v)
        (maskWord (n^4) p R (circleSize (n^4) p) (n^4)
          (shiftMaskState (n^4) p (circleSize (n^4) p) (n^4) v ((circleSize (n^4) p/2 : ℕ) : ZMod (circleSize (n^4) p)))) : ℝ) := by sorry
