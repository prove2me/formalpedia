-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
-- name    : LanglandsTunnell.CubicInduction.exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/03a92c34-13ec-5245-a59b-4250fc7f94c2
-- title:
--   Skew-Hermitian diagonal action on homogeneous symbols tensored with W
-- statement:
--   Let $W$ be a finite-dimensional complex vector space, and let $\rho_{ij}$ ($i,j\in\{0,1,2\}$) be $\mathbb{C}$-linear endomorphisms of $W$ satisfying $\rho_{ji}x=-\rho_{ij}x$ for all $x$ and the relation $\rho_{01}^2x+\rho_{02}^2x+\rho_{12}^2x=-2x$. Let $B:W\times W\to\mathbb{C}$ satisfy $B(zw_1+w_2,w')=zB(w_1,w')+B(w_2,w')$, $B(w',w)=\overline{B(w,w')}$, $\operatorname{Re}B(w,w)>0$ for $w\neq0$, and $B(\rho_{ij}x,y)=-B(x,\rho_{ij}y)$. Fix $N\in\mathbb{N}$. Put $P=\mathbb{C}[X_{(a,b)}:a\le b]$, let $Y$ be the symmetric $3\times3$ matrix over $P$ with entries $Y_{ab}=X_{(a,b)}$ for $a\le b$ (and $Y_{ab}=X_{(b,a)}$ otherwise), let $K_{ij}=E_{ij}-E_{ji}$, and let $D_{ij}$ be the $\mathbb{C}$-derivation of $P$ sending the variable indexed by $(a,b)$ to the $(a,b)$ entry of $K_{ij}Y-YK_{ij}$. On $P\otimes_{\mathbb{C}}W$ set $\theta_{ij}=\mathrm{id}\otimes\rho_{ij}-D_{ij}\otimes\mathrm{id}$, and let $S$ be the $\mathbb{C}$-span of the tensors $q\otimes w$ with $q$ homogeneous of degree $N$. The assertion is: $S$ is a finite $\mathbb{C}$-module; each $\theta_{ij}$ maps $S$ into $S$; there exists $B':(P\otimes W)\times(P\otimes W)\to\mathbb{C}$ which, for arguments in $S$, is additive and $\mathbb{C}$-homogeneous in the first variable, Hermitian, has $\operatorname{Re}B'(w,w)>0$ for $0\neq w\in S$, and makes every $\theta_{ij}$ skew; and for all $q\in P$, $w\in W$, $$(\theta_{01}^2+\theta_{02}^2+\theta_{12}^2)(q\otimes w)+2(q\otimes w)=\sum_{\kappa\in\{01,02,12\}}\bigl(D_\kappa^2q\otimes w-2\,D_\kappa q\otimes\rho_\kappa w\bigr),$$ the doubling being written as a sum of two equal terms.
--
--   This packages the diagonal action of the rotation derivations $\theta_{ij}$ on symbols tensored with a unitary module: finite-dimensionality and invariance of the degree-$N$ piece, a positive-definite Hermitian form for which the $\theta_{ij}$ are skew (the Fischer-type form on $P$ paired with $B$), and the reduction of the diagonal Casimir on pure tensors to derivation terms. It feeds the two lemmas on membership in the span of invariants and on the Casimir decomposition of homogeneous tensors used in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LanglandsTunnell.CubicInduction.exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (N : ℕ) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    let θ : Fin 3 → Fin 3 → (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W →ₗ[ℂ] MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      fun i j => TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id
    let S : Submodule ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W | ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}
    Module.Finite ℂ S ∧
    (∀ i j : Fin 3, ∀ x ∈ S, θ i j x ∈ S) ∧
    (∃ B' : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ), ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ w' ∈ S, B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w ∈ S, ∀ w' ∈ S, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w ∈ S, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ i j : Fin 3, ∀ w ∈ S, ∀ w' ∈ S, B' (θ i j w) w' = -B' w (θ i j w'))) ∧
    (∀ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
      (θ 0 1 ∘ₗ θ 0 1 + θ 0 2 ∘ₗ θ 0 2 + θ 1 2 ∘ₗ θ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
        ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
        ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
        ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))) := by sorry
