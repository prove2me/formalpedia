-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_fredholm_alternative
-- name    : HunterPDE.Elliptic.fredholm_alternative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:52:58.506326+00:00
-- url     : https://prove2.me/theorems/92b83027-77c6-44bb-a3a8-b0f0e22f5b7d
-- title:
--   Theorem 4.24 — Fredholm alternative for uniformly elliptic operators on bounded domains
-- statement:
--   Let $\Omega$ be a bounded open set in $\mathbb{R}^n$ and $L$ a uniformly elliptic operator (4.16) whose coefficients satisfy (4.17). Let $L^*$ be the adjoint operator (4.22) and $\lambda \in \mathbb{R}$. Then one of the following two alternatives holds.
--
--   1. The only weak solution of $L^*v - \lambda v = 0$ is $v = 0$. For every $f \in L^2(\Omega)$ there is a unique weak solution $u \in H^1_0(\Omega)$ of $Lu - \lambda u = f$. In particular, the only solution of $Lu - \lambda u = 0$ is $u = 0$.
--   2. The equation $L^*v - \lambda v = 0$ has a nonzero weak solution $v$. The solution spaces of $Lu - \lambda u = 0$ and $L^*v - \lambda v = 0$ are finite-dimensional and have the same dimension. For $f \in L^2(\Omega)$, the equation $Lu - \lambda u = f$ has a weak solution $u \in H^1_0(\Omega)$ if and only if
--   $$(f, v)_{L^2} = \int_\Omega f v\,dx = 0 \quad \text{for every } v \in H^1_0(\Omega) \text{ with } L^*v - \lambda v = 0,$$
--   and if a solution exists it is not unique.
--
--   This is the solvability theory of the Dirichlet problem for general second-order elliptic operators: uniqueness is equivalent to existence for all data, and otherwise the data must satisfy finitely many orthogonality conditions.
--
--   **Formalization Note.** "Weak solution" is Definition 4.19 with $\mu = -\lambda$: for $L$ with the bilinear form (4.20) (`form P`), for $L^*$ with $a^*(u,v) = a(v,u)$ (`formAdj P`). $f \in L^2(\Omega)$ is an element of `Lp ℝ 2 (volume.restrict Ω)` acting by $\phi \mapsto \int_\Omega f\phi$. Solution spaces are `solutionSpace`, subspaces of $H^1_0(\Omega)$; finite-dimensionality of each is asserted separately from the equality of their `finrank`s. The Lean name of $\lambda$ is `lam`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 107, Theorem 4.24

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory

namespace HunterPDE.Elliptic

/-- Theorem 4.24 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 107 (Fredholm alternative):
let `Ω` be a bounded open set in `ℝⁿ`, `L` a uniformly elliptic operator (4.16) with coefficients
satisfying (4.17), `L*` its adjoint (4.22) and `λ ∈ ℝ` (`lam` in Lean). Then one of two alternatives holds.
(1) The only weak solution of `L*v − λv = 0` is `v = 0`; for every `f ∈ L²(Ω)` there is a unique
weak solution `u ∈ H¹₀(Ω)` of `Lu − λu = f`; in particular the only solution of `Lu − λu = 0` is
`u = 0`.
(2) `L*v − λv = 0` has a nonzero weak solution `v`; the solution spaces of `Lu − λu = 0` and
`L*v − λv = 0` are finite-dimensional and have the same dimension; for `f ∈ L²(Ω)`, `Lu − λu = f`
has a weak solution `u ∈ H¹₀(Ω)` iff `(f, v)_{L²} = 0` for every `v ∈ H¹₀(Ω)` with
`L*v − λv = 0`, and if a solution exists it is not unique.
"Weak solution" is Definition 4.19 with `μ = −λ`: for `L` the bilinear form (4.20) `form P`, for
`L*` the form (4.21) `formAdj P`; `f ∈ L²(Ω)` acts by `φ ↦ ∫_Ω f φ dx` (Definition 4.1). -/
theorem fredholm_alternative {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : Coeffs n) (hP : P.Admissible Ω)
    (hell : P.UniformlyElliptic Ω) (lam : ℝ) :
    ((∀ v : H10 n Ω, IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v → v = 0) ∧
      (∀ f : Lp ℝ 2 (volume.restrict Ω),
        ∃! u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u) ∧
      (∀ u : H10 n Ω, IsWeakSolution (form P) (-lam) (fun _ => 0) u → u = 0)) ∨
    ((∃ v : H10 n Ω, v ≠ 0 ∧ IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v) ∧
      FiniteDimensional ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) ∧
      FiniteDimensional ℝ (solutionSpace (Ω := Ω) (formAdj P) (-lam)) ∧
      Module.finrank ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) =
        Module.finrank ℝ (solutionSpace (Ω := Ω) (formAdj P) (-lam)) ∧
      ∀ f : Lp ℝ 2 (volume.restrict Ω),
        ((∃ u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u) ↔
          ∀ v : H10 n Ω, IsWeakSolution (formAdj P) (-lam) (fun _ => 0) v →
            l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ) v = 0) ∧
        ∀ u : H10 n Ω, IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u →
          ∃ u' : H10 n Ω, u' ≠ u ∧
            IsWeakSolution (form P) (-lam) (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u') := by sorry

end HunterPDE.Elliptic
