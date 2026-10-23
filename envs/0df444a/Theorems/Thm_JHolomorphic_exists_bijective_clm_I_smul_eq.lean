-- Prove2me | Theorems.Thm_JHolomorphic_exists_bijective_clm_I_smul_eq
-- name    : JHolomorphic.exists_bijective_clm_I_smul_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T10:52:25.909601+00:00
-- url     : https://prove2.me/theorems/de117bde-d6f4-44db-8878-7e476cd42b82
-- title:
--   A linear complex structure on a $2n$-dimensional real space is isomorphic to $\mathbb{C}^n$
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space with $\dim_{\mathbb{R}} E = 2n$, and let $J:E\to E$ be a real-linear map with $J\circ J=-\mathrm{Id}_E$. Then there is a real-linear bijection $T:\mathbb{C}^n\to E$ such that
--   $$T(i\,w)=J(T w)\qquad\text{for all } w\in\mathbb{C}^n.$$
--
--   This is the normal form of a linear complex structure: it lets one transport problems about a varying complex structure on $E$ to the standard structure on $\mathbb{C}^n$, for instance in local trivializations of Cauchy–Riemann type operators.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)` with its real structure; $T$ has type `EuclideanSpace ℂ (Fin n) →L[ℝ] E` and bijectivity is `Function.Bijective T`.
-- source:
--   Standard linear algebra; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace JHolomorphic

/-- A real vector space `E` of dimension `2n` carrying a linear complex structure `J` (`J² = -1`)
admits a real-linear bijection `T : ℂⁿ → E` with `T (i w) = J (T w)` for all `w`. -/
theorem exists_bijective_clm_I_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (J : E →L[ℝ] E)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ∃ T : EuclideanSpace ℂ (Fin n) →L[ℝ] E, Function.Bijective T ∧
      ∀ w, T (Complex.I • w) = J (T w) := by
  sorry

end JHolomorphic
