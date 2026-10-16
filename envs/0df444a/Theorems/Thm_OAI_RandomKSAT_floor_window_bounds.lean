-- Prove2me | Theorems.Thm_OAI_RandomKSAT_floor_window_bounds
-- name    : OAI.RandomKSAT.floor_window_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:32:30.945269+00:00
-- url     : https://prove2.me/theorems/db764e33-d4c6-408f-a624-9c37f9906062
-- title:
--   Arithmetic bounds for the window parameters $Q=\lfloor an/4\rfloor$, $V=Rn$, $M=2Rn$
-- statement:
--   Let $a$ be a real number with $0<a\le1$, and let $n,R$ be natural numbers with $R\ge1$ and $an\ge8$. Put
--   $$
--   Q=\Big\lfloor\frac{an}{4}\Big\rfloor ,
--   $$
--   the largest integer not exceeding $an/4$.
--
--   **Theorem.** The following hold.
--
--   1. $an/8\le Q$.
--   2. $Q\le an/4$.
--   3. $2Q\le 2Rn$.
--   4. $Q+Rn\le 2Rn+1$.
--   5. $Q\le 2Rn$.
--   6. The window coefficient is bounded below independently of $n$:
--   $$
--   \frac{a}{16\,(2R+1)^2}\le\frac{Q\,(2Rn+1-Q-Rn)}{(2Rn+1)^2}.
--   $$
--
--   These are the parameter conditions for the window argument behind the linear variance lower bound for the random $k$-SAT failure time, with $M=2Rn$ clauses, upper window end $V=Rn$ and $Q$ as above: item 4 is $Q+V\le M+1$, items 3 and 5 are $2Q\le M$ and $Q\le M$, and item 6 shows that the coefficient $p=Q(M+1-Q-V)/(M+1)^2$ of the bystander variance bound is at least the constant $a/(16(2R+1)^2)$.
--
--   **Formalization Note** $Q$ is introduced by `let Q := ⌊a*n/4⌋₊` (the natural-number floor). Items 3–5 are inequalities between natural numbers, while items 1, 2 and 6 are real inequalities; in item 6 the difference $2Rn+1-Q-Rn$ is computed in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FailureWindows.lean#L89-L137

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

theorem OAI.RandomKSAT.floor_window_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {n R : ℕ} (hR : 1 ≤ R) (hn : 8 ≤ a*n) :
    let Q := ⌊a*n/4⌋₊
    (a*n/8 ≤ (Q:ℝ)) ∧ ((Q:ℝ) ≤ a*n/4) ∧
      2*Q ≤ 2*R*n ∧ Q+R*n ≤ 2*R*n+1 ∧ Q ≤ 2*R*n ∧
      a/(16*((2*R:ℕ)+1:ℝ)^2) ≤
        (Q:ℝ)*((2*R*n:ℕ)+1-Q-R*n:ℝ)/((2*R*n:ℕ)+1:ℝ)^2 := by sorry
