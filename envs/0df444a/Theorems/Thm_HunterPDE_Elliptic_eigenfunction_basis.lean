-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_eigenfunction_basis
-- name    : HunterPDE.Elliptic.eigenfunction_basis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:53:54.131336+00:00
-- url     : https://prove2.me/theorems/1babb401-c1c7-4749-9a1e-062d2272f944
-- title:
--   Theorem 4.25 — eigenvalues λₖ → ∞ and an orthonormal eigenbasis of L²(Ω) for symmetric elliptic L
-- statement:
--   Let $\Omega$ be a bounded open set in $\mathbb{R}^n$ and $L$ the symmetric, uniformly elliptic operator
--   $$Lu = -\sum_{i,j=1}^n \partial_i(a_{ij}\partial_j u) + cu \qquad (4.32)$$
--   with $a_{ij} = a_{ji}$ and $a_{ij}, c \in L^\infty(\Omega)$. Then $L$ has a nondecreasing sequence of real eigenvalues of finite multiplicity
--   $$\lambda_1 \le \lambda_2 \le \lambda_3 \le \cdots, \qquad \lambda_k \to \infty,$$
--   and there is an orthonormal basis $\{\phi_k\}$ of $L^2(\Omega)$ consisting of eigenfunctions $\phi_k \in H^1_0(\Omega)$ with $L\phi_k = \lambda_k\phi_k$ (weakly: $a(\phi_k, v) = \lambda_k(\phi_k, v)_{L^2}$ for all $v \in H^1_0(\Omega)$).
--
--   This is the spectral theory of the Dirichlet problem for self-adjoint elliptic operators, the basis of eigenfunction expansions.
--
--   **Formalization Note.** The page prints $\lambda_1 < \lambda_2$; that is not proved in the notes and is false for disconnected $\Omega$ (two disjoint equal balls), so the chain is stated non-strict. $\Omega$ is assumed nonempty and $n \ge 1$ (otherwise $L^2(\Omega)$ is finite-dimensional and no basis is indexed by $\mathbb{N}$). Indices are 0-based (`eig 0` is $\lambda_1$). $b = 0$ is the hypothesis `P.b = 0`. Finite multiplicity is `FiniteDimensional` of each eigenspace.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 108–109, Eq. (4.32), Theorem 4.25

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory Filter

namespace HunterPDE.Elliptic

/-- Theorem 4.25 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 109, in the setting of §4.10
(p. 108): `Ω` a bounded open set, `L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu) + c u` symmetric and uniformly elliptic
(4.32), `aᵢⱼ = aⱼᵢ`, `aᵢⱼ, c ∈ L^∞(Ω)` (so `b = 0`). Then `L` has a nondecreasing sequence of real
eigenvalues `λ₁ ≤ λ₂ ≤ …` of finite multiplicity with `λₖ → ∞`, and there is an orthonormal basis
`{φₖ}` of `L²(Ω)` of eigenfunctions `φₖ ∈ H¹₀(Ω)` with `L φₖ = λₖ φₖ` (weakly:
`a(φₖ, v) = λₖ (φₖ, v)_{L²}` for all `v ∈ H¹₀(Ω)`, Definition 4.19 with `μ = −λₖ`, `f = 0`).
The page prints `λ₁ < λ₂`; that is false for disconnected `Ω` and not proved, so the chain is
stated non-strict. `Ω` is assumed nonempty and `n ≥ 1` (otherwise `L²(Ω)` is
finite-dimensional and has no orthonormal basis indexed by `ℕ`).
Indices are 0-based: Lean's `eig 0` is the book's `λ₁`. -/
theorem eigenfunction_basis {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hn : 1 ≤ n) (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (P : Coeffs n)
    (hP : P.Admissible Ω)
    (hb : P.b = 0) (hell : P.UniformlyElliptic Ω) :
    ∃ eig : ℕ → ℝ, Monotone eig ∧ Tendsto eig atTop atTop ∧
      (∀ k, FiniteDimensional ℝ (solutionSpace (Ω := Ω) (form P) (-eig k))) ∧
      ∃ φ : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict Ω)), ∀ k,
        ∃ u : H10 n Ω, toL2 u = φ k ∧ IsWeakSolution (form P) (-eig k) (fun _ => 0) u := by sorry

end HunterPDE.Elliptic
