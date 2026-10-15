-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_killFraction_le_pow
-- name    : OAI.FixedClauseThreshold.killFraction_le_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:48:54.805991+00:00
-- url     : https://prove2.me/theorems/9ceb37bf-cef9-4965-823b-ae5455d89578
-- title:
--   Power bound $\kappa(b,n,r)\le(b/2n)^r$ for the kill fraction
-- statement:
--   For natural numbers $b,n,r$ let
--   $$
--   \kappa(b,n,r)=\frac{\binom br}{\binom nr\,2^r}
--   $$
--   be the kill fraction: the probability that a uniformly random proper $r$-clause on $n$ variables (distinct variables, independent fair signs) kills a nonempty set of assignments that has exactly $b$ forced variables.
--
--   **Theorem.** If $b\le n$, $r\le n$ and $n\ge1$, then
--   $$
--   \kappa(b,n,r)\le\Big(\frac{b}{2n}\Big)^r .
--   $$
--
--   The right-hand side is the killing probability one would get if the $r$ variables of the clause were drawn with replacement. Since $b\le n$, the bound gives in particular $\kappa(b,n,r)\le2^{-r}$. In the comparison between a shorter clause and a block of longer clauses, this bound shows that a non-negligible killing probability forces the fraction $b/n$ of forced variables to be large.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Replacement.lean#L56-L76

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.killFraction_le_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ ((b : ℝ) / (2 * n)) ^ r := by sorry
