-- Prove2me | Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
-- name    : MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/e2572a78-a6d6-5d71-8073-7940701f1b72
-- title:
--   Existence of a Gotzmann bound for a Hilbert polynomial
-- statement:
--   Fix $n \in \mathbb{N}$ and a polynomial $P \in \mathbb{Q}[t]$. For a commutative ring $A$ and an ideal $I$ of $A[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n+1)) A`, write `piece I d` for the quotient of the $A$-module of forms of degree $d$ by those forms that lie in $I$, i.e. the degree-$d$ graded piece of $A[x]/I$. Assume that $P$ is realised as a Hilbert polynomial in the following sense: there are a field $K$, an ideal $I$ of $K[x_0,\dots,x_n]$ that contains every homogeneous component of each of its elements, and an index $d_1$, such that $\dim_K(\mathrm{piece}\ I\ d) = P(d)$ (as rational numbers, after casting) for all $d \ge d_1$. The conclusion asserts the existence of $D_0 \in \mathbb{N}$ such that for every $e \ge D_0$ two things hold. First, for every field $K$ and every ideal $J$ of $K[x_0,\dots,x_n]$ which is the span of a set $s$ of polynomials all homogeneous of degree $e$, the equality $\dim_K(\mathrm{piece}\ J\ e) = P(e)$ forces $\dim_K(\mathrm{piece}\ J\ (e+1)) \le P(e+1)$. Second, this bound is attained: there are a field $K$ and an ideal $J$ of $K[x_0,\dots,x_n]$ spanned by forms of degree $e$ with $\dim_K(\mathrm{piece}\ J\ e) = P(e)$ and $\dim_K(\mathrm{piece}\ J\ (e+1)) = P(e+1)$.
--
--   This is the existence of a Gotzmann number for a Hilbert polynomial $P$ of a graded quotient of a polynomial ring in $n+1$ variables: in all sufficiently large degrees $e$, the value $P(e+1)$ is exactly the Macaulay growth bound for ideals generated in degree $e$ with Hilbert value $P(e)$, and the bound is sharp. It is used in the construction and analysis of the Hilbert functor, in particular in the results on closed immersions with flat quotient and prescribed Hilbert function that characterise membership in the relevant ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ e : ℕ, D₀ ≤ e →
      (∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) →
        (Module.finrank K (piece J (e + 1)) : ℚ) ≤ P.eval ((e : ℚ) + 1)) ∧
      ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) ∧
        (Module.finrank K (piece J (e + 1)) : ℚ) = P.eval ((e : ℚ) + 1) := by sorry
