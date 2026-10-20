-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_observedRegularStatistic_bound
-- name    : OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:10:01.450307+00:00
-- url     : https://prove2.me/theorems/8bdea8ee-40ab-4de9-b4f9-809b785a76af
-- title:
--   The normalized boundary statistic of the $b$-ary tree is bounded at each depth
-- statement:
--   Let $b\in\mathbb{N}$ and $\lambda\in\mathbb{R}$. Depth-$0$ observations are spins, and depth-$(\ell+1)$ observations are finite multisets of depth-$\ell$ observations. The statistic $\widehat T_\ell$ is defined as follows. $\widehat T_0(i)=\sigma(i)$, where $\sigma(0)=2$ and $\sigma(1)=\sigma(2)=-1$. For a multiset $s$ with exactly $b$ elements, $\widehat T_{\ell+1}(s)=\frac{1}{b\lambda}\sum_{o\in s}\widehat T_\ell(o)$; for any other multiset, $\widehat T_{\ell+1}(s)=0$. Then for every depth $\ell$ there is a constant $C\ge0$ with
--   $$
--   \bigl|\widehat T_\ell(o)\bigr|\le C\qquad\text{for all depth-}\ell\text{ observations } o .
--   $$
--
--   Boundedness makes $\widehat T_\ell$ integrable under any observation law, so it can serve as a test statistic in the estimator lower bound for the advantage.
--
--   **Formalization Note** With Lean's convention $x/0=0$, the statement also holds when $b\lambda=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean#L88-L100

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Experiment

theorem OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound (b : ℕ) (lam : ℝ) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ o, |observedRegularStatistic b lam ℓ o| ≤ C := by sorry
