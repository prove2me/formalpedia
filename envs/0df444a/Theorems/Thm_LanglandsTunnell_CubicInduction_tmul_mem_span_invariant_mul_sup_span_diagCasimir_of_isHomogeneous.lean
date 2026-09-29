-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
-- name    : LanglandsTunnell.CubicInduction.tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/06f1de8c-9754-5ea6-b0d2-68eba7352113
-- title:
--   Homogeneous symbols split off invariants modulo the diagonal Casimir
-- statement:
--   Let $W$ be a finite-dimensional complex vector space equipped with operators $\rho_{ij}\in\operatorname{End}_{\mathbb C}(W)$ for $i,j\in\{0,1,2\}$ satisfying, pointwise, $\rho_{ji}=-\rho_{ij}$, $[\rho_{01},\rho_{02}]=-\rho_{12}$, $[\rho_{01},\rho_{12}]=\rho_{02}$, $[\rho_{02},\rho_{12}]=-\rho_{01}$ and $\rho_{01}^2+\rho_{02}^2+\rho_{12}^2=-2\cdot\mathrm{id}$, and let $B:W\times W\to\mathbb C$ be a form that is linear in its first argument, satisfies $B(w',w)=\overline{B(w,w')}$, has $\operatorname{Re}B(w,w)>0$ for $w\neq0$, and for which every $\rho_{ij}$ is skew: $B(\rho_{ij}x,y)=-B(x,\rho_{ij}y)$. Write $P=\mathbb C[X_{(a,b)}:a\le b]$, let $Y$ be the symmetric $3\times3$ matrix over $P$ with entries $X_{(a,b)}$ for $a\le b$ (and $X_{(b,a)}$ otherwise), put $K_{ij}=E_{ij}-E_{ji}$, and let $D_{ij}$ be the $\mathbb C$-derivation of $P$ sending the variable indexed by $(a,b)$ to the $(a,b)$ entry of $K_{ij}Y-YK_{ij}$. Then for every $n\in\mathbb N$, every $p\in P$ homogeneous of degree $n+1$ and every $v\in W$, the element $p\otimes v$ of $P\otimes_{\mathbb C}W$ lies in the sum of two submodules: the span of all $(sq)\otimes w$ with $s$ homogeneous of degree $a$ and annihilated by all $D_{ij}$, $q$ homogeneous of degree $d\le2$ and $a+d=n+1$; and the span of all elements $\sum_{\kappa\in\{01,02,12\}}\bigl(D_\kappa^2q\otimes w-(D_\kappa q\otimes\rho_\kappa w+D_\kappa q\otimes\rho_\kappa w)\bigr)$ with $q$ homogeneous of degree $n+1$ and $w\in W$.
--
--   The second span is the image on degree-$(n+1)$ symbols of the Casimir $\Omega+2$ of the diagonal $\mathfrak{so}(3)$-action on $P\otimes W$, so the statement says that every homogeneous symbol is congruent, modulo that image, to a combination of products of $D$-invariants with factors of degree at most two; it is the inductive step underlying the finiteness statement [`LanglandsTunnell.CubicInduction.finiteDimensional_ker_rotationCasimir_add_two_gKSpan_of_isCentreFinite`](thm.html#LanglandsTunnell.CubicInduction.finiteDimensional_ker_rotationCasimir_add_two_gKSpan_of_isCentreFinite) in the Langlands–Tunnell part of the development. The proof cites the spectral splitting for skew operators on a positive-definite Hermitian space, the construction of the Hermitian form on $P_m\otimes W$, and the invariant-span statement for vectors killed by $\Omega+2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LanglandsTunnell.CubicInduction.tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hrel₁ : ∀ x : W, ρ 0 1 (ρ 0 2 x) - ρ 0 2 (ρ 0 1 x) = -ρ 1 2 x)
    (hrel₂ : ∀ x : W, ρ 0 1 (ρ 1 2 x) - ρ 1 2 (ρ 0 1 x) = ρ 0 2 x)
    (hrel₃ : ∀ x : W, ρ 0 2 (ρ 1 2 x) - ρ 1 2 (ρ 0 2 x) = -ρ 0 1 x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (n : ℕ) (p : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (hp : p.IsHomogeneous (n + 1)) (v : W) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    p ⊗ₜ[ℂ] v ∈
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W |
          ∃ (a d : ℕ) (s q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
            s.IsHomogeneous a ∧ (∀ i j : Fin 3, D i j s = 0) ∧ q.IsHomogeneous d ∧ d ≤ 2 ∧ a + d = n + 1 ∧
              x = (s * q) ⊗ₜ[ℂ] w} ⊔
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W |
          ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous (n + 1) ∧
            x = ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
                ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
                ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))} := by sorry
