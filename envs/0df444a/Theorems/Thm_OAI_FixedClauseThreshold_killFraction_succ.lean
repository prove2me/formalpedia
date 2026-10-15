-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_killFraction_succ
-- name    : OAI.FixedClauseThreshold.killFraction_succ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:48:32.696235+00:00
-- url     : https://prove2.me/theorems/2bacf975-086e-47fa-a4c0-705c68df6bb5
-- title:
--   Ratio recursion for the kill fraction $\binom br/(\binom nr2^r)$
-- statement:
--   For natural numbers $b,n,r$ let
--   $$
--   \kappa(b,n,r)=\frac{\binom br}{\binom nr\,2^r}
--   $$
--   be the kill fraction. If a nonempty set of assignments of $n$ Boolean variables has exactly $b$ forced variables (variables on which all its members agree), then $\kappa(b,n,r)$ is the probability that a uniformly random proper $r$-clause, on $r$ distinct variables with independent fair signs, is violated by every assignment in the set. Write $(b-r)_+=\max(b-r,0)$.
--
--   **Theorem.** If $r+1\le n$, then
--   $$
--   \kappa(b,n,r+1)=\kappa(b,n,r)\cdot\frac{(b-r)_+}{2\,(n-r)} .
--   $$
--
--   In probabilistic terms, once $r$ forced variables have been chosen, an additional variable is forced with probability $(b-r)_+/(n-r)$ and receives the opposing sign with probability $1/2$. The recursion is the basis for the power bound $\kappa(b,n,r)\le(b/2n)^r$ and for the lower bound $\kappa(b,n,r+1)\ge\kappa(b,n,r)\,b/\big(2n(r+1)\big)$ when $r+1\le b$, which are used to compare a single shorter clause with a block of longer clauses.
--
--   **Formalization Note** The factor $b-r$ is natural-number subtraction cast to $\mathbb{R}$, hence $0$ when $r\ge b$; in that case both sides are $0$. The hypothesis $r+1\le n$ makes $n-r\ge1$ and $\binom nr,\binom n{r+1}$ positive, so no division by zero occurs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Replacement.lean#L27-L46

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.killFraction_succ {b n r : ℕ} (hrn : r + 1 ≤ n) :
    killFraction b n (r + 1) =
      killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by sorry
