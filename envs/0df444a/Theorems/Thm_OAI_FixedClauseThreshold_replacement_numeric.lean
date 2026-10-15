-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_replacement_numeric
-- name    : OAI.FixedClauseThreshold.replacement_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:49:36.154203+00:00
-- url     : https://prove2.me/theorems/ce9905d6-f7ff-4078-9d15-7bea4a27944b
-- title:
--   One shorter clause kills at most as often as a block of $g$ longer clauses, up to error $a^{-r}$
-- statement:
--   For natural numbers $b,v,r$ let $\kappa(b,v,r)=\binom br/(\binom vr\,2^r)$ be the kill fraction. If a nonempty set of assignments of $v$ Boolean variables has exactly $b$ forced variables, then $\kappa(b,v,r)$ is the probability that one uniformly random proper $r$-clause (distinct variables, independent fair signs) is violated by every assignment in the set. Likewise $1-(1-\kappa(b,v,r+1))^g$ is the probability that at least one of $g$ independent uniformly random proper $(r+1)$-clauses is violated by every assignment in the set.
--
--   **Theorem.** Let $b,v,r,g$ be natural numbers and $a$ a real number such that
--   $$
--   1\le r<v,\qquad b\le v,\qquad a>0,\qquad \frac{1}{v+1}\le a^{-r},\qquad 2(r+1)\,a\le g .
--   $$
--   Then
--   $$
--   \kappa(b,v,r)-a^{-r}\le1-\big(1-\kappa(b,v,r+1)\big)^g .
--   $$
--
--   The inequality is purely numerical, and it holds uniformly in the number $b$ of forced variables. Up to the additive error $a^{-r}$, a single random clause of length $r$ is no more likely to kill a solution set than a block of $g\ge2(r+1)a$ independent random clauses of length $r+1$. It is designed for $r=k-1$, $v=n-1$, $a=n^{1/k}$ and $g=\lceil2kn^{1/k}\rceil$. There the error is $a^{-r}=n^{-(k-1)/k}$, and the result is used to replace a clause shortened by erasing one literal with a block of fresh $k$-clauses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Replacement.lean#L228-L280

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.replacement_numeric {b v r g : ℕ} {a : ℝ}
    (hr : 1 ≤ r) (hrv : r < v) (hbv : b ≤ v) (ha : 0 < a)
    (hsmall : 1 / (v + 1 : ℝ) ≤ a⁻¹ ^ r)
    (hg : 2 * (r + 1 : ℝ) * a ≤ (g : ℝ)) :
    killFraction b v r - a⁻¹ ^ r ≤ 1 - (1 - killFraction b v (r + 1)) ^ g := by sorry
