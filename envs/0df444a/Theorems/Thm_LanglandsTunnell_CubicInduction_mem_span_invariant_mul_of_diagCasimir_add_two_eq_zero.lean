-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero
-- name    : LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f57cfc29-257c-5d8b-88f8-8de3cae92ae9
-- title:
--   Kernel of Ω+2 on degree n+1 symbols
-- statement:
--   Let $W$ be a finite-dimensional complex vector space equipped with operators $\rho_{ij}\in\operatorname{End}_{\mathbb C}(W)$, indexed by $i,j\in\{0,1,2\}$, which satisfy $\rho_{ji}x=-\rho_{ij}x$, the three commutator identities $[\rho_{01},\rho_{02}]=-\rho_{12}$, $[\rho_{01},\rho_{12}]=\rho_{02}$, $[\rho_{02},\rho_{12}]=-\rho_{01}$ (pointwise on $W$), and the Casimir identity $\rho_{01}^2x+\rho_{02}^2x+\rho_{12}^2x=-2x$; let $B:W\times W\to\mathbb C$ satisfy $B(zw_1+w_2,w')=zB(w_1,w')+B(w_2,w')$, $B(w',w)=\overline{B(w,w')}$, $\operatorname{Re}B(w,w)>0$ for $w\neq 0$, and $B(\rho_{ij}x,y)=-B(x,\rho_{ij}y)$. Write $P=\mathbb C[Y_{ab}:a\le b]$ for the polynomial ring on the indices $\{(a,b):a\le b\}$ in $\mathrm{Fin}\,3\times\mathrm{Fin}\,3$, let $Y$ be the symmetric matrix with entries $Y_{ab}$, let $K_{ij}=E_{ij}-E_{ji}$, let $D_{ij}$ be the $\mathbb C$-derivation of $P$ sending the variable indexed by $(a,b)$ to the $(a,b)$ entry of $K_{ij}Y-YK_{ij}$, and put $\theta_{ij}=\mathrm{id}\otimes\rho_{ij}-D_{ij}\otimes\mathrm{id}$ on $P\otimes_{\mathbb C}W$. Let $n\in\mathbb N$ and let $k$ lie in the span $S$ of the tensors $q\otimes w$ with $q$ homogeneous of degree $n+1$. The assertion is: if $(\theta_{01}^2+\theta_{02}^2+\theta_{12}^2)k+2k=0$, then $k$ lies in the $\mathbb C$-span of the elements $(sq)\otimes w$ with $s$ homogeneous of some degree $a$ and killed by every $D_{ij}$, $q$ homogeneous of some degree $d\le 2$, and $a+d=n+1$.
--
--   This is the kernel half of the separation-of-variables statement for the pair $(\mathfrak{gl}_3,\mathfrak{so}_3)$ in the type-one case: on symbols of degree $n+1$ with values in a unitary $\mathfrak{so}(3)$-module of Casimir $-2$, the kernel of the shifted diagonal Casimir is spanned by products of $\mathfrak{so}(3)$-invariant polynomials with harmonic-type factors of degree at most two. It is used by [`LanglandsTunnell.CubicInduction.tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous`](thm.html#LanglandsTunnell.CubicInduction.tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous), which combines it with the orthogonal eigenspace decomposition of the same Casimir operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero
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
    (n : ℕ) (k : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :
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
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W | ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous (n + 1) ∧ x = q ⊗ₜ[ℂ] w}
    k ∈ S →
    (θ 0 1 ∘ₗ θ 0 1 + θ 0 2 ∘ₗ θ 0 2 + θ 1 2 ∘ₗ θ 1 2) k + (2 : ℂ) • k = 0 →
    k ∈ Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W |
          ∃ (a d : ℕ) (s q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
            s.IsHomogeneous a ∧ (∀ i j : Fin 3, D i j s = 0) ∧ q.IsHomogeneous d ∧ d ≤ 2 ∧ a + d = n + 1 ∧
              x = (s * q) ⊗ₜ[ℂ] w} := by sorry
