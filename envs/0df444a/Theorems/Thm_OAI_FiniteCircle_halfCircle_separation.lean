-- Prove2me | Theorems.Thm_OAI_FiniteCircle_halfCircle_separation
-- name    : OAI.FiniteCircle.halfCircle_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:35:01.100026+00:00
-- url     : https://prove2.me/theorems/ac3120c5-f288-4c98-88ac-5954bec98d7d
-- title:
--   Rotating a half-circle word by $\theta$ forces deficit at least $\|\theta\|/4$
-- statement:
--   Let $M\ge 1$ be even and write $\mathbb{Z}_M=\mathbb{Z}/M\mathbb{Z}$. For $x\in\mathbb{Z}_M$ let $\|x\|=\min(\bar x,\,M-\bar x)$ be its circular distance to $0$, where $\bar x\in\{0,\dots,M-1\}$ is the representative of $x$, and let $c_\circ(x)=\|x\|/M\in[0,\tfrac12]$ be the *circle cost*. For $v\in\mathbb{Z}_M$ let $H_v\in\{0,1\}^M$ be the *half-circle word* whose $i$-th letter ($0\le i<M$) is $1$ exactly when $\overline{i-v}<M/2$; that is, $H_v$ is the indicator word of the arc $\{v,v+1,\dots,v+M/2-1\}$ of the cycle. For words $x,y$ let $\mathrm{lcs}(x,y)$ be the maximal length of a common (not necessarily contiguous) subsequence, and let $\mathrm{def}(x,y)=|x|-\mathrm{lcs}(x,y)$ be the *deficit*.
--
--   **Theorem.** For all $v,\theta\in\mathbb{Z}_M$,
--
--   $$
--   \frac{M\,c_\circ(\theta)}{4}\le \mathrm{def}\bigl(H_v,\,H_{v+\theta}\bigr).
--   $$
--
--   Since $M\,c_\circ(\theta)=\|\theta\|$, the inequality says that the half-circle word and its rotation by $\theta$ cannot be aligned as common subsequences without discarding at least $\|\theta\|/4$ letters of each. It is the level-zero case of the separation estimates for the hierarchical mask and excluded-sum word families, whose level-zero phase cost is exactly $c_\circ$.
--
--   **Formalization Note** $H_v$ is `List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M))`, $\|\theta\|$ is `θ.valMinAbs.natAbs` and $c_\circ$ is `circleCost`; evenness is the hypothesis `M = 2*(M/2)`, and the natural-number deficit is cast to the reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L402-L417

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.halfCircle_separation {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v θ : ZMod M) :
    (M:ℝ)*circleCost θ/4 ≤
      (deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) : ℝ) := by sorry
