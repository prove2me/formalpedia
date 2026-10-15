-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_auxiliaryProbability_center_lower
-- name    : OAI.FixedClauseThreshold.auxiliaryProbability_center_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:08:35.941287+00:00
-- url     : https://prove2.me/theorems/dd9505c1-fb85-4ca9-a8ec-ffbc40e68c3d
-- title:
--   Below the lifetime center, the auxiliary $k$-SAT model is satisfiable with probability bounded away from zero
-- statement:
--   Let $k\ge3$ and $n\ge k+1$ be integers with $2\binom k2\le n$, and let $m\in\mathbb N$. A *proper $k$-clause* on $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each, satisfied by an assignment that agrees with at least one sign. With $L_k=2^{k+1}$ and $M=L_kn$ independent uniform proper $k$-clauses $C_1,\dots,C_M$, let $\Lambda$ be the number of $j\le M$ for which $C_1,\dots,C_j$ are simultaneously satisfiable, and $c_{n,k}=\mathbb E[\Lambda]/n$. Put
--
--   $$
--   \delta_k=\frac{k-2}{4k},\qquad \eta_k=\frac{k-2}{2k},\qquad V_k=2L_k^3\,k\,(2k+L_k+2).
--   $$
--
--   An *auxiliary $k$-clause* is an ordered $k$-tuple of independent uniformly random literals on $x_1,\dots,x_n$ (variables may repeat), and $Q_n(m)$ denotes the probability that $m$ independent auxiliary $k$-clauses are simultaneously satisfiable. Assume
--
--   $$
--   V_k\,n^{-\eta_k}\le\tfrac12\qquad\text{and}\qquad m+n^{1-\delta_k}\le n\,c_{n,k}.
--   $$
--
--   Then
--
--   $$
--   Q_n(m)\ \ge\ \frac12\exp\Big(-2\cdot2^{k+1}\binom k2\Big).
--   $$
--
--   So at clause counts at least one fluctuation window $n^{1-\delta_k}$ below $n\,c_{n,k}$, the auxiliary model is satisfiable with a probability bounded below by a positive constant depending only on $k$. This transfers the concentration of the proper-clause model to the auxiliary model, where partition interpolation is available.
--
--   **Formalization Note** $Q_n(m)$ is `auxiliaryProbability n k m`; $V_kn^{-\eta_k}$, $n^{1-\delta_k}$ and $c_{n,k}$ are `concentrationError n k`, `fluctuationWindow n k` and `center n k`. The bound is `transferLower k` $=$ `transferFactor k / 2`, written with `capMultiplier k` $=2^{k+1}$ and `repeatPairs k` $=\binom k2$ (a real number), and the hypothesis $2\binom k2\le n$ is `2 * repeatPairs k ≤ n` over the reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Transfer.lean#L297-L316

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.auxiliaryProbability_center_lower {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (herror : concentrationError n k ≤ 1 / 2)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    transferLower k ≤ auxiliaryProbability n k m := by sorry
