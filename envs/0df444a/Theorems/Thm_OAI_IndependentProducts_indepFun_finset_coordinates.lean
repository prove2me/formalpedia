-- Prove2me | Theorems.Thm_OAI_IndependentProducts_indepFun_finset_coordinates
-- name    : OAI.IndependentProducts.indepFun_finset_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:05:07.982303+00:00
-- url     : https://prove2.me/theorems/75bff7d8-b9a7-4f19-bbbb-590b5a3705fe
-- title:
--   A product of functions of finitely many coordinates is independent of any other coordinate
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$, let $\mathcal E$ be the set of nonroot vertices of the tree of finite sequences of positive integers, and equip $\mathbb{R}^{\mathcal E}$ with the infinite product measure $\mu^{\otimes\mathcal E}$, under which the coordinates $\omega_d$ $(d\in\mathcal E)$ are independent with common law $\mu$. Let $s\subseteq\mathcal E$ be a finite set, let $(f_d)_{d\in\mathcal E}$ be a family of Borel measurable functions $f_d:\mathbb{R}\to\mathbb{R}$, and let $e\in\mathcal E$ with $e\notin s$.
--
--   Then, under $\mu^{\otimes\mathcal E}$, the two random variables
--
--   $$\omega\longmapsto\prod_{d\in s}f_d(\omega_d)\qquad\text{and}\qquad\omega\longmapsto\omega_e$$
--
--   are independent.
--
--   This is the form of independence used throughout the analysis of path products: a path product, or any product of functions of the coordinates along a path, is independent of every coordinate off that path. It yields factorizations such as $\mathbb{E}[\Pi_v\,g(\omega_e)]=\mathbb{E}[\Pi_v]\;\mathbb{E}[g(\omega_e)]$.
--
--   **Formalization Note** The sample space is the type `Sample` of real functions on nonroot vertices, the measure is `productMeasure μ`, defined with Mathlib's `Measure.infinitePi`, and independence is `IndepFun`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/PathMoments.lean#L218-L240

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem OAI.IndependentProducts.indepFun_finset_coordinates (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ e, Measurable (f e)) (e : Edge) (he : e ∉ s) :
    IndepFun (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (fun ω : Sample => ω e)
      (productMeasure μ) := by sorry
