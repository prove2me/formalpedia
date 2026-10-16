-- Prove2me | Theorems.Thm_OAI_RandomKSAT_deletionQ_poly_bound
-- name    : OAI.RandomKSAT.deletionQ_poly_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:14:23.770448+00:00
-- url     : https://prove2.me/theorems/feaa1018-0c42-43fc-bf3f-4f4afad9d420
-- title:
--   Quadratic bound for the deletion constant
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
--   Q\big(\max(1,Z)\big)\ \le\ (C+1)\,(1+Z)^2.
--   $$
--
--   The deletion constant enters the conditional second-moment bound for forced-prefix rewards with $d=\max(1,Z)$, where $Z$ is the random number of clauses meeting the root variables. This inequality replaces the fractional power $d^{\beta}$ by a polynomial in $Z$, so that the bound can be averaged over random root data with elementary moment estimates.
--
--   **Formalization Note** $Q(d)$ is `deletionQ (r+1) d`, $C$ is `lifetimeC (r+1)`, $\beta$ is `lifetimeBeta (r+1)`, and the power $d^{\beta}$ is `Real.rpow`; $\max(1,Z)$ is taken in $\mathbb N$ and then cast to $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/WeightedRewards.lean#L382-L394

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

theorem OAI.RandomKSAT.deletionQ_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    deletionQ (r+1) (max 1 Z) ≤ (lifetimeC (r+1)+1)*(1+(Z : ℝ))^2 := by sorry
