-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_ae_gramSchmidt_ne_zero
-- name    : OAI.SubsphereRegression.ae_gramSchmidt_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:12:49.627874+00:00
-- url     : https://prove2.me/theorems/a45a9b6b-a161-49d9-93cd-0a96a77126f4
-- title:
--   Gram–Schmidt vectors of product-measure samples are almost everywhere nonzero under a local mass bound
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a finite measure on $E$ and let $a\in\mathbb{R}$. Assume that $\nu$ satisfies the *local mass bound with exponent $a$*, that is, $\nu(\bar B(t,r))\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$, where $\bar B(t,r)$ is the closed ball and $\operatorname{supp}\nu$ is the support of $\nu$ (the set of points all of whose neighbourhoods have positive $\nu$-measure); assume also that $\operatorname{supp}\nu\subseteq\bar B(0,1)$.
--
--   Fix a base point $p\in E$ and $n\in\mathbb{N}$ with $n\le a$. For $v=(v_0,\dots,v_{n-1})\in E^{n}$ let $u_0(v),\dots,u_{n-1}(v)$ be the Gram–Schmidt vectors of the differences $v_0-p,\dots,v_{n-1}-p$ (the $j$-th one is $v_j-p$ minus its orthogonal projection onto the span of the earlier differences). Then, with $\nu^{\otimes n}$ the product measure on $E^{n}$,
--   $$u_i(v)\ne0\quad\text{for all }0\le i<n,\qquad\text{for }\nu^{\otimes n}\text{-almost every }v\in E^{n}.$$
--
--   All Gram–Schmidt vectors are nonzero exactly when the input vectors are linearly independent, so the conclusion says that $\nu^{\otimes n}$-almost every tuple $(v_0,\dots,v_{n-1})$ is affinely independent together with the base point $p$ (for a probability measure $\nu$: $n$ independent samples are almost surely in general position with $p$); successive affine degeneracies form null sets as long as the number of points does not exceed the exponent $a$. Consequently the Gram determinant of the differences $v_i-p$ is positive almost everywhere, and its negative powers are finite almost everywhere.
--
--   **Formalization Note** The Gram–Schmidt vectors are Mathlib's `gramSchmidt ℝ (fun j => v j - p) i`, the product measure is `Measure.pi (fun _ => ν)`, and the hypothesis is `(n : ℝ) ≤ a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gram.lean#L313-L348

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.ae_gramSchmidt_ne_zero {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 := by sorry
