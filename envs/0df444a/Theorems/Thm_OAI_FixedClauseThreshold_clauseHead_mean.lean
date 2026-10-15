-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_clauseHead_mean
-- name    : OAI.FixedClauseThreshold.clauseHead_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:53:32.676903+00:00
-- url     : https://prove2.me/theorems/afa3b3b7-9278-4729-b5d0-e2b0b7e4d795
-- title:
--   Averaging over a random proper clause by conditioning on whether it contains the first variable
-- statement:
--   Let $0<k\le v$. Consider the Boolean variables $x_0,x_1,\dots,x_v$, and for $r\le v$ let $\mathcal C_{v,r}$ denote the set of proper $r$-clauses on $x_1,\dots,x_v$, a proper $r$-clause being a choice of $r$ distinct variables with a sign (a required truth value) for each. Every proper $k$-clause $C$ on $x_0,\dots,x_v$ is of exactly one of two kinds:
--
--   1. $C$ does not involve $x_0$; then it is a proper $k$-clause $C'\in\mathcal C_{v,k}$ on $x_1,\dots,x_v$;
--   2. $C$ involves $x_0$ with some sign $b\in\{0,1\}$; then its remaining literals form a proper $(k-1)$-clause $Q\in\mathcal C_{v,k-1}$.
--
--   This defines a bijection $\operatorname{split}$ from the proper $k$-clauses on $x_0,\dots,x_v$ onto the disjoint union $\mathcal C_{v,k}\sqcup(\mathcal C_{v,k-1}\times\{0,1\})$. For every function $f:\mathcal C_{v,k}\sqcup(\mathcal C_{v,k-1}\times\{0,1\})\to\mathbb R$, with all expectations taken uniformly,
--
--   $$
--   \mathbb E_{C}\big[f(\operatorname{split}C)\big]=\Big(1-\frac{k}{v+1}\Big)\,\mathbb E_{C'\in\mathcal C_{v,k}}\big[f(C')\big]+\frac{k}{v+1}\,\mathbb E_{Q\in\mathcal C_{v,k-1}}\,\mathbb E_{b\in\{0,1\}}\big[f(Q,b)\big].
--   $$
--
--   In words: a uniformly random proper $k$-clause on $v+1$ variables contains $x_0$ with probability $k/(v+1)$; conditionally on this, its remaining part is a uniform proper $(k-1)$-clause and the sign of $x_0$ is an independent fair coin, while conditionally on the complement it is a uniform proper $k$-clause on the other $v$ variables. This is the one-step recursion used for random formulas in which one variable is deleted or erased.
--
--   **Formalization Note** The first variable is `0 : Fin (v + 1)`, and $\operatorname{split}$ is `clauseHeadSplit hk`, the forward map of the equivalence `clauseHeadEquiv`; the two kinds are `Sum.inl` and `Sum.inr`. Expectations are `uniformMean`. The hypotheses $0<k\le v$ make both $\mathcal C_{v,k}$ and $\mathcal C_{v,k-1}$ nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/ClauseProcess.lean#L394-L416

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.clauseHead_mean {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (f : (ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)) → ℝ) :
    uniformMean (fun C : ProperClause (v + 1) k => f (clauseHeadSplit hk C)) =
      (1 - (k : ℝ) / (v + 1)) * uniformMean (fun C => f (Sum.inl C)) +
      ((k : ℝ) / (v + 1)) *
        uniformMean (fun Q => uniformMean (fun b : Bool => f (Sum.inr (Q, b)))) := by sorry
