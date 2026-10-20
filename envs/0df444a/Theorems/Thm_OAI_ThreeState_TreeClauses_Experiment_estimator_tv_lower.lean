-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_estimator_tv_lower
-- name    : OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:12:57.021439+00:00
-- url     : https://prove2.me/theorems/09898c1c-0f6e-43e4-9595-cb88cafd8a92
-- title:
--   A bounded statistic correlated with spin $0$ forces posterior advantage at least $1/(3C)$
-- statement:
--   Let $\alpha$ be a countable type with measurable singletons and $p=(p_0,p_1,p_2)$ three discrete laws on $\alpha$, with uniform mixture $\bar p=\frac13\sum_ip_i$. Let $m(a)$ be the posterior message ($m_i(a)=p_i(a)/\bar p(a)$, or $(1,1,1)$ if $\bar p(a)=0$), $\nu$ the law of $m(a)$ under $a\sim\bar p$, and $\mathrm{tv}(m)=\frac16\sum_i|m_i-1|$.
--
--   Let $f:\alpha\to\mathbb{R}$ be bounded, $|f|\le B$, and let $C>0$. Assume
--   $$
--   \mathbb{E}_{\bar p}[f]=0,\qquad \mathbb{E}_{p_0}[f]=2,\qquad \mathbb{E}_{\bar p}[f^2]\le C .
--   $$
--   Then
--   $$
--   \int\mathrm{tv}\,d\nu\ \ge\ \frac{1}{3C}.
--   $$
--
--   A statistic that is centred under the uniform mixture but has mean $2$ given spin $0$ certifies that the posterior is, on average, far from uniform. The variance $C$ controls by how much. This is the second-moment method for reconstruction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/InformationLoss.lean#L213-L255

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
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Radial
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower (p : Spin → PMF α) {f : α → ℝ} {B C : ℝ}
    (hB : ∀ a, |f a| ≤ B) (hC : 0 < C)
    (hzero : (∫ a, f a ∂(discreteMarginal p).toMeasure) = 0)
    (hroot : (∫ a, f a ∂(p 0).toMeasure) = 2)
    (hsecond : (∫ a, f a^2 ∂(discreteMarginal p).toMeasure) ≤ C) :
    1/(3*C) ≤ ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by sorry
