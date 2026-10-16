-- Prove2me | Theorems.Thm_OAI_RandomKSAT_exists_lower_scale
-- name    : OAI.RandomKSAT.exists_lower_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:35:09.668123+00:00
-- url     : https://prove2.me/theorems/a0709024-c2b4-41b6-80f0-793fa6665761
-- title:
--   An integer scale $R$ with $U(k)\le 2R$ and $2(1-2^{-k})^R<1$
-- statement:
--   Let $k\ge1$ be an integer and put
--   $$
--   U(k)=\frac{\log 2}{-\log\big(1-2^{-k}\big)} .
--   $$
--
--   **Theorem.** There is a natural number $R$ such that
--   $$
--   R\ge1,\qquad U(k)\le 2R,\qquad 2\,\big(1-2^{-k}\big)^R<1 .
--   $$
--
--   A uniform random clause of width $k$ is satisfied by a fixed assignment with probability $1-2^{-k}$, so after $Rn$ independent clauses on $n$ variables the expected number of satisfying assignments is $2^n(1-2^{-k})^{Rn}=\big(2(1-2^{-k})^R\big)^n$. The third condition makes this decay exponentially in $n$, so the random formula is unsatisfiable after $Rn$ clauses with high probability, while the second condition ensures that the cap $B=2R$ is at least the threshold $U(k)$. Since $\log(1-2^{-k})<0$, the third condition is in fact equivalent to $R>U(k)$. The scale $R$ fixes the window parameters $M=2Rn$ and $V=Rn$ in the linear variance lower bound for the random $k$-SAT failure time.
--
--   **Formalization Note** $U(k)$ is `U k = Real.log 2 / (-Real.log (1 - ((2:ℝ)^k)⁻¹))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FailureWindows.lean#L153-L165

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
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.exists_lower_scale (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ, 1 ≤ R ∧ U k ≤ 2*(R:ℝ) ∧ 2*(1-((2:ℝ)^k)⁻¹)^R < 1 := by sorry
