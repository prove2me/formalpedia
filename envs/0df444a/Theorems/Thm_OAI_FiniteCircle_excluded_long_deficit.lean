-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_long_deficit
-- name    : OAI.FiniteCircle.excluded_long_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:45:01.542956+00:00
-- url     : https://prove2.me/theorems/c63a7ba0-2744-46c8-99a4-233daa980889
-- title:
--   A half-turn shift of all phases forces deficit at least $n^{-3n^4}$ times the length of an excluded-coordinate circle word
-- statement:
--   Let $n\ge10^6$ be an integer such that $n^4$ is even (equivalently, $n$ is even), and put $h=n^4$. Let $(p_{l,k})_{l,k\in\mathbb{N}}$ be a *standing prime array* for $h$: for $1\le l\le h$ and $0\le k<h$ the numbers $p_{l,k}$ are primes with $h^3<p_{l,k}\le2h^3$, these $h^2$ primes are pairwise distinct, and $p_{l,k}=1$ for every other pair $(l,k)$. Put $P_l=\prod_{k<h}p_{l,k}$, let $M=2\prod_{l=1}^{h}P_l$ (so every $p_{l,k}$ divides $M$ and $M$ is even), and fix an integer $R\ge1$. For words $x,y$ let $\operatorname{lcs}(x,y)$ be the length of a longest common subsequence and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$ the deficit.
--
--   *Excluded-coordinate circle words.* A state of depth $0$ is a phase $v\in\mathbb{Z}/M$, and a state $v$ of depth $l\ge1$ is a family $(v_i)_{0\le i<h}$ of states of depth $l-1$ (a rooted $h$-ary tree with phases at its leaves). For $\theta\in\mathbb{Z}/M$, $v+\theta$ denotes the state obtained by adding $\theta$ to every leaf phase. The word $X_l(v)$ is defined recursively:
--
--   1. $X_0(v)$ is the word of length $M$ whose $b$-th letter ($0\le b<M$) is the pair $(b,c_b)$, where $c_b=1$ if and only if the residue of $b-v$ in $\{0,\dots,M-1\}$ is less than $M/2$;
--   2. for $l\ge1$, $X_l(v)$ is the concatenation, over $s=0,1,\dots,RP_l-1$ and, for each $s$, over $i=0,1,\dots,h-1$, of the word $X_{l-1}\big(v_i+\tau_l(s,i)\big)$ with every letter labelled by $i$, where
--
--   $$
--   \tau_l(s,i)=\sum_{j\ne i}\frac{M}{p_{l,j}}\,(s\bmod p_{l,j})\ \in\mathbb{Z}/M
--   $$
--
--   (the sum runs over $0\le j<h$, $j\ne i$: coordinate $i$ is excluded).
--
--   Every word $X_l(v)$ has the same length $E_l$, where $E_0=M$ and $E_l=R\,P_l\,h\,E_{l-1}$.
--
--   **Theorem.** For every state $v$ of depth $h$,
--
--   $$
--   \frac{E_h}{n^{3n^4}}\le\operatorname{def}\Big(X_h(v),\,X_h\big(v+\tfrac M2\big)\Big).
--   $$
--
--   Thus shifting every phase by half a turn destroys, in the longest-common-subsequence sense, at least a fraction $n^{-3n^4}$ of the word. This is the long-move separation used in the lower bound on the $\ell^1$ distortion of the family of encoded excluded-coordinate words.
--
--   **Formalization Note** The prime array is `StandingPrimes (n^4) p`, $M$ is `circleSize (n^4) p`, $X_l$ is `excludedWord (n^4) p R M l`, $E_l$ is `excludedLength (n^4) p R M l`, the shift is `shiftExcludedState`, $\tau_l$ is `excludedTranslation` (with the exact natural-number quotients $M/p$), and $\operatorname{def}$ is `deficit` (truncated subtraction, harmless since $\operatorname{lcs}(x,y)\le|x|$). The evenness hypothesis is stated as $n^4=2\lfloor n^4/2\rfloor$, and the half turn is the class of the natural number $\lfloor M/2\rfloor=M/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/DeficitLower.lean#L79-L119

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

theorem OAI.FiniteCircle.excluded_long_deficit {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2))
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {R : ℕ} (hR : 0<R)
    (v : ExcludedState (n^4) (circleSize (n^4) p) (n^4)) :
    (excludedLength (n^4) p R (circleSize (n^4) p) (n^4):ℝ)/(n:ℝ)^(3*n^4) ≤
      (deficit (excludedWord (n^4) p R (circleSize (n^4) p) (n^4) v)
        (excludedWord (n^4) p R (circleSize (n^4) p) (n^4)
          (shiftExcludedState (n^4) (circleSize (n^4) p) (n^4) v ((circleSize (n^4) p/2 : ℕ) : ZMod (circleSize (n^4) p)))) : ℝ) := by sorry
