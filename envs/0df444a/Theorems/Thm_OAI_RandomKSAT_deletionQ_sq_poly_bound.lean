-- Prove2me | Theorems.Thm_OAI_RandomKSAT_deletionQ_sq_poly_bound
-- name    : OAI.RandomKSAT.deletionQ_sq_poly_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:15:38.964078+00:00
-- url     : https://prove2.me/theorems/b2877261-63d2-4ff6-9cbc-872e99d6f187
-- title:
--   Cubic bound for the square of the deletion constant
-- statement:
--   Let $r\ge2$ be an integer. Put $K=(2^{r+1}r)^{r}$, $C=4(2K)^{1/r}$ and $\beta=\frac{r+1}{r}$, and for a natural number $d$ define the *deletion constant*
--
--   $$
--   Q(d)=(C+1)\,d^{\beta}.
--   $$
--
--   **Theorem.** For every natural number $Z$,
--
--   $$
--   Q\big(\max(1,Z)\big)^2\ \le\ (C+1)^2\,(1+Z)^3.
--   $$
--
--   This is the companion of the quadratic bound $Q(\max(1,Z))\le(C+1)(1+Z)^2$. It is sharper than squaring that bound because $2\beta\le 3$, and it is used to control the leading term $8Q^2h(M)$ of the conditional second-moment bound by the third moment of $1+Z$.
--
--   **Formalization Note** $Q(d)$ is `deletionQ (r+1) d`, $C$ is `lifetimeC (r+1)`, $\beta$ is `lifetimeBeta (r+1)`, and the power $d^{\beta}$ is `Real.rpow`; $\max(1,Z)$ is taken in $\mathbb N$ and then cast to $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/WeightedRewards.lean#L396-L408

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.deletionQ_sq_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    (deletionQ (r+1) (max 1 Z))^2 ≤ (lifetimeC (r+1)+1)^2*(1+(Z : ℝ))^3 := by sorry
