-- Prove2me | Theorems.Thm_OAI_IndependentProducts_measurePreserving_sampleSelector
-- name    : OAI.IndependentProducts.measurePreserving_sampleSelector
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:35:46.874497+00:00
-- url     : https://prove2.me/theorems/78c95b2f-89d3-4ef6-9593-a4767eefa33a
-- title:
--   Coordinatewise selection from independent product samples preserves the product law
-- statement:
--   Let $\mathcal E$ be the set of nonroot vertices of the tree of finite sequences of positive integers, let $\mu$ be a probability measure on $\mathbb R$, and let $P_\mu=\mu^{\otimes\mathcal E}$ be the product measure on the sample space $\mathbb R^{\mathcal E}$ (one independent $\mu$-distributed coordinate per vertex). Let $\kappa$ be a finite set and $s:\mathcal E\to\kappa$ an arbitrary map. For a family $\boldsymbol\omega=(\omega_k)_{k\in\kappa}$ of samples define the selected sample $\Phi_s(\boldsymbol\omega)\in\mathbb R^{\mathcal E}$ by
--   $$
--   \Phi_s(\boldsymbol\omega)(e)=\omega_{s(e)}(e)\qquad(e\in\mathcal E).
--   $$
--
--   **Theorem.** The map $\Phi_s:(\mathbb R^{\mathcal E})^\kappa\to\mathbb R^{\mathcal E}$ is measurable and measure preserving from $P_\mu^{\otimes\kappa}$ to $P_\mu$:
--
--   $$
--   (\Phi_s)_{*}\big(P_\mu^{\otimes\kappa}\big)=P_\mu.
--   $$
--
--   In words: if $|\kappa|$ independent samples are drawn and every coordinate of a new sample is copied from one of them according to a fixed rule, the new sample has the same law as a single sample. This is the measure-theoretic core of resampling arguments in which old coordinates, fresh coordinates on exit vertices, and fresh coordinates below them are stitched into one sample.
--
--   **Formalization Note** The map is `fun ω : κ → Sample => fun e => ω (s e) e`, and the claim is `MeasurePreserving` from `Measure.pi (fun _ : κ => productMeasure μ)` to `productMeasure μ`, where `productMeasure μ` is `Measure.infinitePi (fun _ => μ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean#L166-L187

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem OAI.IndependentProducts.measurePreserving_sampleSelector {κ : Type uκ} [Fintype κ] (s : Edge → κ) :
    MeasurePreserving (fun ω : κ → Sample => fun e => ω (s e) e)
      (Measure.pi (fun _ : κ => productMeasure μ)) (productMeasure μ) := by sorry
