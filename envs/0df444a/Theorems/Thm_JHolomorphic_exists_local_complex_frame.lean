-- Prove2me | Theorems.Thm_JHolomorphic_exists_local_complex_frame
-- name    : JHolomorphic.exists_local_complex_frame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:33:29.960634+00:00
-- url     : https://prove2.me/theorems/6af51efe-df1a-4838-9087-6bd48cb51b78
-- title:
--   A smooth family of linear complex structures is locally trivial
-- statement:
--   Let $E$ be a finite-dimensional real normed space with $\dim_{\mathbb{R}}E=2n$, and let $\bar J:\mathbb{C}\to\operatorname{End}_{\mathbb{R}}(E)$ be $C^\infty$ on the open unit disc $D$ with $\bar J(z)^2=-\mathrm{Id}$ for $z\in D$. Then there are $0<\rho\le1$ and maps $\Psi:\mathbb{C}\to\operatorname{Hom}_{\mathbb{R}}(\mathbb{C}^n,E)$, $\Psi^{-1}:\mathbb{C}\to\operatorname{Hom}_{\mathbb{R}}(E,\mathbb{C}^n)$, both $C^\infty$ on $D_\rho$, such that for every $z\in D_\rho$: $\Psi^{-1}(z)\Psi(z)=\mathrm{Id}$, $\Psi(z)\Psi^{-1}(z)=\mathrm{Id}$, and
--   $$\Psi(z)(i\,w)=\bar J(z)\,\Psi(z)\,w\qquad(w\in\mathbb{C}^n).$$
--
--   This is a local smooth complex trivialization of a varying linear complex structure; it reduces Cauchy–Riemann type equations with a point-dependent complex structure $\bar J(z)$ to equations for $\mathbb{C}^n$-valued maps with the standard structure $i$.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`; smoothness is `ContDiffOn ℝ ∞ _ (ball 0 ρ)` in the operator-norm topology, and the inverse relations are stated pointwise on vectors.
-- source:
--   Standard; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

/-- Let `E` have real dimension `2n` and let `J̄ : ℂ → End_ℝ(E)` be smooth on the open unit disc with
`J̄(z)² = -1`. Then for some `0 < ρ ≤ 1` there are smooth maps `Ψ : D_ρ → Hom_ℝ(ℂⁿ, E)` and
`Ψ⁻¹ : D_ρ → Hom_ℝ(E, ℂⁿ)`, inverse to each other at every point, with `Ψ(z)(i w) = J̄(z) Ψ(z) w`. -/
theorem exists_local_complex_frame {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E) :
    ∃ ρ > (0 : ℝ), ρ ≤ 1 ∧ ∃ Ψ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ Ψi : ℂ → E →L[ℝ] EuclideanSpace ℂ (Fin n),
        ContDiffOn ℝ ∞ Ψ (ball 0 ρ) ∧ ContDiffOn ℝ ∞ Ψi (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : ℂ) ρ, (∀ v, Ψi z (Ψ z v) = v) ∧ (∀ x, Ψ z (Ψi z x) = x) ∧
          ∀ w, Ψ z (Complex.I • w) = Jbar z (Ψ z w) := by
  sorry

end JHolomorphic
