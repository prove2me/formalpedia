-- Prove2me | Theorems.Thm_OAI_SpinAngle_Analytic_three_projection_angle_of_density_mixtures
-- name    : OAI.SpinAngle.Analytic.three_projection_angle_of_density_mixtures
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:21:11.945723+00:00
-- url     : https://prove2.me/theorems/e6b63fb7-b70d-41bc-8808-5f3e3eaf54b2
-- title:
--   Three-projection angle bound from two mixture dominations, a support factorization and a commuting middle factor
-- statement:
--   Let $\mathcal{A}$ be a unital C*-algebra with its standard order (a partial order making it a star-ordered ring in which nonnegative elements have nonnegative spectrum, so $x\le y$ means that $y-x$ is positive). A projection is an element $p$ with $p=p^{*}=p^{2}$. Let $I$ and $J$ be finite index sets.
--
--   **Theorem.** Let $h,k,p\in\mathcal{A}$ be projections, let $w_i\ge0$ ($i\in I$) and $z_j\ge0$ ($j\in J$) be real weights, let $r_i,v_i,t_i,q_i\in\mathcal{A}$ ($i\in I$) and $s_j\in\mathcal{A}$ ($j\in J$) be elements, and let $g\ge0$ and $\phi\ge0$ be real numbers. Assume:
--
--   1. $h\le\sum_{i\in I}w_i\,r_i^{*}r_i$ and $k\le\sum_{j\in J}z_j\,s_js_j^{*}$;
--   2. $v_it_i=q_i$ and $r_iq_i=r_i$ for every $i\in I$;
--   3. every $t_i$ commutes with $k$ and with $p$;
--   4. $\|pt_i\|^{2}\le g$ for every $i\in I$, and $\|r_iv_is_j\|^{2}\le\phi$ for all $i\in I$, $j\in J$.
--
--   Then
--   $$\|hkp\|^{2}\le\min\Big\{1,\ \Big(\sum_{i\in I}w_i\Big)\Big(\sum_{j\in J}z_j\Big)\,g\,\phi\Big\}.$$
--
--   This abstract inequality is the engine of the angle bound for column, row and global type projections on a board of cells. There $h$ and $k$ are the column and row type projections, dominated by mixtures of product states written as $r_i^{*}r_i$ and $s_js_j^{*}$; $t_i$ is a tensor power of the square root of an averaged state, $v_i$ its pseudo-inverse and $q_i$ its support; $g$ bounds the interaction of the averaged state with the global projection $p$, and $\phi$ bounds the normalized cell operators.
--
--   **Formalization Note** The algebra is any type with `CStarAlgebra`, `PartialOrder`, `StarOrderedRing` and `NonnegSpectrumClass ℝ` instances, projections are `IsStarProjection`, and the constant $\phi$ is the variable `phi`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Compression.lean#L158-L197

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

theorem OAI.SpinAngle.Analytic.three_projection_angle_of_density_mixtures
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (h k p : A) (hh : IsStarProjection h) (hk : IsStarProjection k)
    (hp : IsStarProjection p)
    (w : ι → ℝ) (z : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ j, 0 ≤ z j)
    (r v t q : ι → A) (s : κ → A)
    (hH : h ≤ ∑ i, w i • (star (r i) * r i))
    (hK : k ≤ ∑ j, z j • (s j * star (s j)))
    (hvt : ∀ i, v i * t i = q i) (hrq : ∀ i, r i * q i = r i)
    (htk : ∀ i, Commute (t i) k) (htp : ∀ i, Commute (t i) p)
    (g phi : ℝ) (hg : 0 ≤ g) (hphi : 0 ≤ phi)
    (hglobal : ∀ i, ‖p * t i‖ ^ 2 ≤ g)
    (hcell : ∀ i j, ‖r i * v i * s j‖ ^ 2 ≤ phi) :
    ‖h * k * p‖ ^ 2 ≤ min 1 ((∑ i, w i) * (∑ j, z j) * g * phi) := by sorry
