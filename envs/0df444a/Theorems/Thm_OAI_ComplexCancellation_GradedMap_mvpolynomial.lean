-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_GradedMap_mvpolynomial
-- name    : OAI.ComplexCancellation.GradedMap.mvpolynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:57:15.526716+00:00
-- url     : https://prove2.me/theorems/6138403c-ab39-40a7-8604-c0c1a25ddc4c
-- title:
--   Algebra maps sending each variable to a homogeneous element preserve weighted homogeneity
-- statement:
--   Let $k$ be a commutative ring and let $R$ be a commutative $k$-algebra with a $\mathbb{Z}$-grading $R=\bigoplus_{e\in\mathbb{Z}}R_e$ by $k$-submodules, compatible with multiplication ($R_eR_{e'}\subseteq R_{e+e'}$ and $1\in R_0$). Let $(X_i)_{i\in I}$ be variables indexed by an arbitrary set $I$, let $w:I\to\mathbb{Z}$ assign an integer weight to each variable, and let $f:k[X_i : i\in I]\to R$ be a $k$-algebra homomorphism with $f(X_i)\in R_{w(i)}$ for every $i\in I$. A polynomial $p$ is weighted homogeneous of weight $e$ if every monomial $\prod_iX_i^{m_i}$ occurring in $p$ with nonzero coefficient satisfies $\sum_im_i\,w(i)=e$ (the zero polynomial is weighted homogeneous of every weight).
--
--   **Theorem.** For every $e\in\mathbb{Z}$ and every polynomial $p\in k[X_i : i\in I]$ that is weighted homogeneous of weight $e$,
--
--   $$
--   f(p)\in R_e .
--   $$
--
--   This is the basic tool for checking that explicit elements given by polynomial formulas are homogeneous: one only has to know the degrees of the images of the variables. It is used to show that homomorphisms from weighted polynomial rings to graded algebras (Laurent polynomial rings, special fibres, affine modifications) respect the gradings.
--
--   **Formalization Note** The grading is `G : ℤ → Submodule k R` with `[GradedAlgebra G]`, the polynomial ring is `MvPolynomial ι k`, and weighted homogeneity is Mathlib's `IsWeightedHomogeneous w p e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/GradedMap.lean#L11-L26

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation

open OAI OAI.ComplexCancellation
open MvPolynomial
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

theorem OAI.ComplexCancellation.GradedMap.mvpolynomial {ι : Type*} (G : ℤ → Submodule k R) [GradedAlgebra G]
    (w : ι → ℤ) (f : MvPolynomial ι k →ₐ[k] R)
    (hX : ∀ i, f (X i) ∈ G (w i)) {p : MvPolynomial ι k} {e : ℤ}
    (hp : IsWeightedHomogeneous w p e) : f p ∈ G e := by sorry
