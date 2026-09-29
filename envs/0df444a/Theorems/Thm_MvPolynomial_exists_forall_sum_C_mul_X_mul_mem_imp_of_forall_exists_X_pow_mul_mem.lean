-- Prove2me | Theorems.Thm_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
-- name    : MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/ec75bebd-dc87-5742-a026-4f46a1dc67da
-- title:
--   A linear form that is a non-zero-divisor modulo a saturated homogeneous ideal
-- statement:
--   Fix $n \in \mathbb{N}$, an infinite field $K$, and an ideal $I$ of the polynomial ring $K[x_0,\dots,x_n]$ in $n+1$ variables indexed by `Fin (n + 1)`, graded by total degree. Two hypotheses are imposed on $I$: first, $I$ is homogeneous in the sense that for every $p \in I$ and every $i \in \mathbb{N}$ the degree-$i$ homogeneous component of $p$ again lies in $I$; second, $I$ is saturated with respect to the variables, in the sense that whenever $F$ is homogeneous of some degree $d$ and for each index $i$ there exists an exponent $N$ (allowed to depend on $i$) with $x_i^{N} F \in I$, then already $F \in I$. The conclusion asserts the existence of scalars $a_0,\dots,a_n \in K$ such that the linear form $\ell = \sum_{i} a_i x_i$ has the property: for every degree $d$ and every $F$ homogeneous of degree $d$, $\ell \cdot F \in I$ implies $F \in I$. No non-vanishing of the vector $a$ is asserted separately; for $I \neq K[x_0,\dots,x_n]$ it follows from the stated property.
--
--   This is the standard existence of a linear form which is a non-zero-divisor on $K[x_0,\dots,x_n]/I$ for a saturated homogeneous ideal $I$ over an infinite field — classically obtained by prime avoidance, since saturation says the irrelevant maximal ideal is not an associated prime, and here obtained instead through Macaulay's bound and Gotzmann persistence for the Hilbert function, together with the construction of a non-zero polynomial $G$ whose non-vanishing at $a$ guarantees the required property in large degrees. It feeds into the analysis of Hilbert functions of closed subschemes used in the construction of the Hilbert functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
    (n : ℕ) (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (hsat : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) → F ∈ I) :
    ∃ a : Fin (n + 1) → K, ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∑ i : Fin (n + 1), MvPolynomial.C (a i) * MvPolynomial.X i) * F ∈ I → F ∈ I := by sorry
