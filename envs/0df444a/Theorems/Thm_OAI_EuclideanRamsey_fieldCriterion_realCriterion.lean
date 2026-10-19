-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_fieldCriterion_realCriterion
-- name    : OAI.EuclideanRamsey.fieldCriterion_realCriterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:57:28.471417+00:00
-- url     : https://prove2.me/theorems/9b9f403b-12bb-4370-8054-a5b068f8d3e7
-- title:
--   The field tensor criterion implies the real tensor criterion
-- statement:
--   Let $s,d\in\mathbb{N}$ and let $a=(a_0,\dots,a_{s-1})$ be points of $\mathbb{R}^d$ with coordinates $a_{ij}$. Let $K\subseteq\mathbb{R}$ be the subfield generated over $\mathbb{Q}$ by all coordinates $a_{ij}$. Index matrices by the augmented set $\{\ast,1,\dots,d\}$ and let $\hat a_i=(1,a_{i1},\dots,a_{id})$ be the augmented coordinate vector of $a_i$, read in $K$ or in $\mathbb{R}$. For a field $F\in\{K,\mathbb{R}\}$ let $\mu_F:F\otimes_{\mathbb{Q}}F\to F$, $x\otimes y\mapsto xy$, be the multiplication map.
--
--   The *field criterion* $\mathrm{FC}(a)$ asks for a matrix $P$ indexed by the augmented set with entries in $K\otimes_{\mathbb{Q}}K$, and the *real criterion* $\mathrm{RC}(a)$ for such a matrix with entries in $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$, satisfying in the respective ring
--   $$\sum_{\alpha,\beta}\bigl(\hat a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\hat a_i(\beta)\bigr)=0\quad(0\le i<s),\qquad\mu_F(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).$$
--
--   **Theorem.** For every configuration $a$, with no further hypotheses,
--   $$\mathrm{FC}(a)\ \Longrightarrow\ \mathrm{RC}(a).$$
--
--   This is the easy direction of the comparison between the two criteria (the reverse implication is a separate descent argument). In the sufficiency direction of the classification of Ramsey configurations, a field-criterion certificate is first transported to $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ by this result and then used to build the scaled copies that produce monochromatic configurations.
--
--   **Formalization Note** `FieldCriterion a` uses `TensorRing a = Coeff a ⊗[ℚ] Coeff a` with `Coeff a` the intermediate field `coordinateField a` and `multiply a = Algebra.TensorProduct.lmul' ℚ`; `RealCriterion a` uses `ℝ ⊗[ℚ] ℝ` with `arrayEvaluation` and `spatialMultiply`. The augmented index set is `Option (Fin d)`, with `none` in the role of $\ast$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorDescent.lean#L131-L156

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent

open OAI OAI.EuclideanRamsey
universe uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped TensorProduct BigOperators

theorem OAI.EuclideanRamsey.fieldCriterion_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : FieldCriterion a) : RealCriterion a := by sorry
