-- Prove2me | Theorems.Thm_OAI_SpinAngle_Analytic_norm_mul_projection_sq_le_sum
-- name    : OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:19:45.792368+00:00
-- url     : https://prove2.me/theorems/d38545f6-8595-4475-b3ba-424285dba7f7
-- title:
--   Norm of $ap$ for a projection $p$ dominated by a weighted sum of elements $r_i\,r_i^{*}$
-- statement:
--   Let $\mathcal{A}$ be a unital C*-algebra with its standard order: a partial order making $\mathcal{A}$ a star-ordered ring in which nonnegative elements have nonnegative spectrum, so that $x\le y$ means that $y-x$ is positive. An element $p\in\mathcal{A}$ is a projection if $p=p^{*}=p^{2}$.
--
--   **Theorem.** Let $p\in\mathcal{A}$ be a projection, let $I$ be a finite index set, and let $w_i\ge0$ be real weights and $r_i\in\mathcal{A}$ ($i\in I$) be elements with
--   $$p\le\sum_{i\in I}w_i\,r_ir_i^{*}.$$
--   Then for every $a\in\mathcal{A}$,
--   $$\|ap\|^{2}\le\sum_{i\in I}w_i\,\|ar_i\|^{2}.$$
--
--   The lemma turns an order domination of a projection by a weighted sum into a norm bound for an arbitrary element compressed to the range of the projection. In the application $p$ is a type projection and the $r_ir_i^{*}$ are product states, so the norm of $ap$ is controlled by the norms of $a$ against product states.
--
--   **Formalization Note** The algebra is any type with `CStarAlgebra`, `PartialOrder`, `StarOrderedRing` and `NonnegSpectrumClass ℝ` instances, and the projection hypothesis is `IsStarProjection p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Compression.lean#L62-L81

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
variable {A : Type*} [contextInstance35_21 : CStarAlgebra A] [contextInstance35_38 : PartialOrder A] [contextInstance35_55 : StarOrderedRing A]
  [contextInstance36_2 : NonnegSpectrumClass ℝ A]

theorem OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum {ι : Type*} [Fintype ι]
    (a p : A) (hp : IsStarProjection p) (w : ι → ℝ) (r : ι → A)
    (hw : ∀ i, 0 ≤ w i) (hdom : p ≤ ∑ i, w i • (r i * star (r i))) :
    ‖a * p‖ ^ 2 ≤ ∑ i, w i * ‖a * r i‖ ^ 2 := by sorry
