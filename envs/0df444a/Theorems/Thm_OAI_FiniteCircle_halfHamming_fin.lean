-- Prove2me | Theorems.Thm_OAI_FiniteCircle_halfHamming_fin
-- name    : OAI.FiniteCircle.halfHamming_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:33:58.963272+00:00
-- url     : https://prove2.me/theorems/5aa62f79-d1c9-41b4-ae3d-0c6348300af2
-- title:
--   Half-circle disagreements counted over $\{0,\dots,M-1\}$ and over $\mathbb{Z}/M\mathbb{Z}$ agree
-- statement:
--   Let $M\ge 1$ and write $\mathbb{Z}_M=\mathbb{Z}/M\mathbb{Z}$; every $b\in\mathbb{Z}_M$ has a unique representative $\bar b\in\{0,1,\dots,M-1\}$. For $v\in\mathbb{Z}_M$ the *half-circle indicator* $\beta_v:\mathbb{Z}_M\to\{0,1\}$ is
--
--   $$
--   \beta_v(b)=\begin{cases}1 & \text{if } \overline{b-v}<\lfloor M/2\rfloor,\\ 0 & \text{otherwise,}\end{cases}
--   $$
--
--   so $\beta_v$ is the indicator function of the arc $\{v,v+1,\dots,v+\lfloor M/2\rfloor-1\}$ of the cycle $\mathbb{Z}_M$. The *half-circle Hamming distance* of $v,w\in\mathbb{Z}_M$ is $\operatorname{hH}(v,w)=\#\{b\in\mathbb{Z}_M:\beta_v(b)\neq\beta_w(b)\}$.
--
--   **Theorem.** For all $v,w\in\mathbb{Z}_M$,
--
--   $$
--   \#\bigl\{\,i\in\{0,1,\dots,M-1\} : \beta_v(i \bmod M)\neq\beta_w(i \bmod M)\,\bigr\}=\operatorname{hH}(v,w).
--   $$
--
--   The left-hand side is the Hamming distance between the binary words $H_v=\beta_v(0)\beta_v(1)\cdots\beta_v(M-1)$ and $H_w$ of length $M$, which is how the indicators enter statements about words, subsequences and deficits; the right-hand side is a count over the group $\mathbb{Z}_M$, the form in which translation invariance and the exact value of $\operatorname{hH}$ are established. The lemma lets one pass between the two descriptions.
--
--   **Formalization Note** The left side counts `i : Fin M` through the cast `(i.val : ZMod M)`; the right side is `halfHamming v w`, a cardinality over the finite type `ZMod M` (finite because of the instance `NeZero M`, i.e. $M\neq0$). The indicator is `halfBit v b = decide ((b - v).val < M/2)` with natural-number floor division $M/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L374-L389

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

theorem OAI.FiniteCircle.halfHamming_fin {M : ℕ} [NeZero M] (v w : ZMod M) :
    (Finset.univ.filter (fun i : Fin M => halfBit v (i.val : ZMod M) ≠
      halfBit w (i.val : ZMod M))).card = halfHamming v w := by sorry
