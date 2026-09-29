-- Prove2me | Theorems.Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
-- name    : MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/85a4aa44-18d6-587f-937e-ce18db89cafd
-- title:
--   Hilbert function drop along a nonzerodivisor linear form
-- statement:
--   Fix $n\in\mathbb{N}$, a field $K$, and an ideal $J$ of the polynomial ring $K[x_0,\dots,x_n]=$ `MvPolynomial (Fin (n+1)) K`. Assume $J$ is homogeneous in the sense that every homogeneous component $\mathrm{homogeneousComponent}\;i\;p$ of every $p\in J$ again lies in $J$. Let $\ell$ be a polynomial that is homogeneous of degree $1$ (so $\ell=0$ is permitted), and assume the colon condition that for every degree $e$ and every $F$ homogeneous of degree $e$, $\ell F\in J$ implies $F\in J$; that is, $\ell$ acts as a nonzerodivisor on forms modulo $J$. Let $d\in\mathbb{N}$. Here, for an ideal $I$ and a degree $e$, `piece I e` denotes the $K$-vector space $K[x]_e/(I\cap K[x]_e)$, the quotient of the submodule of forms of degree $e$ by the preimage of $I$ under the inclusion of that submodule. The conclusion is the numerical identity
--   $$\dim_K \bigl(K[x]/(J+(\ell))\bigr)_{d+1}+\dim_K\bigl(K[x]/J\bigr)_d=\dim_K\bigl(K[x]/J\bigr)_{d+1},$$
--   where the first term is `piece (J ⊔ Ideal.span {ℓ}) (d + 1)` and the other two are `piece J d` and `piece J (d + 1)`, all dimensions being `Module.finrank K`.
--
--   This is the numerical shadow of the exact sequence $0\to (K[x]/J)_d \xrightarrow{\cdot\ell} (K[x]/J)_{d+1}\to (K[x]/(J+(\ell)))_{d+1}\to 0$ attached to a linear nonzerodivisor, the standard inductive step in arguments computing Hilbert functions of graded quotients. It is used in the construction of the Hilbert functor, in the proof that the graded dimensions of the pieces are eventually given by evaluating a fixed polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
    (n : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcolon : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d → ℓ * F ∈ J → F ∈ J)
    (d : ℕ) :
    Module.finrank K (piece (J ⊔ Ideal.span {ℓ}) (d + 1)) + Module.finrank K (piece J d) =
      Module.finrank K (piece J (d + 1)) := by sorry
