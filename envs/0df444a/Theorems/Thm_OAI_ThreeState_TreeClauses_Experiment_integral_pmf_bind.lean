-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_pmf_bind
-- name    : OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:00:25.587261+00:00
-- url     : https://prove2.me/theorems/2dfaddb7-dd13-4a76-8144-11cb2df67778
-- title:
--   Tower property for bounded functions under a composite discrete law
-- statement:
--   Let $\alpha,\beta$ be countable types with measurable singletons. Let $p$ be a discrete probability distribution on $\alpha$, and $K$ a Markov kernel giving a discrete probability distribution $K(a)$ on $\beta$ for each $a$. Let $f:\beta\to\mathbb{R}$ be bounded, $|f(b)|\le C$ for all $b$. Let $p\gg\!=K$ be the law of $b$ obtained by drawing $a\sim p$ and then $b\sim K(a)$. Then
--   $$
--   \int_\beta f\,d(p\gg\!=K)=\int_\alpha\Bigl(\int_\beta f\,dK(a)\Bigr)dp(a).
--   $$
--
--   This is the law of total expectation for bounded test functions, stated with Lebesgue integrals against the measures of discrete laws. It is the basic tool for computing expectations along the generations of a tree.
--
--   **Formalization Note** The measures are `PMF.toMeasure`; the boundedness constant $C$ is arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/DiscreteLaw.lean#L132-L147

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Radial
variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind (p : PMF α) (K : α → PMF β) {f : β → ℝ} {C : ℝ}
    (hf : ∀ b, |f b| ≤ C) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by sorry
