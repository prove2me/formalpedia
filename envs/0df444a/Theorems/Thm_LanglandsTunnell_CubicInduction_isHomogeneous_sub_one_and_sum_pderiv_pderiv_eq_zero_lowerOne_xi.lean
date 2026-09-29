-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
-- name    : LanglandsTunnell.CubicInduction.isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/774bfc19-93ee-5677-bac5-736191201e81
-- title:
--   Lowering by one preserves harmonicity and homogeneity
-- statement:
--   Fix a triple $\nu \in \mathbb{C}^3$, a natural number $\ell$, and a polynomial $p \in \mathbb{C}[x_0,x_1,x_2]$ which is homogeneous of degree $\ell$ and harmonic, i.e. $\sum_{i<3}\partial_i\partial_i p = 0$. Two auxiliary constructions are introduced locally in the statement. First, the $3\times 3$ matrix $\Xi(\nu,p)$ over $\mathbb{C}[x_0,x_1,x_2]$ whose $(c,c)$ entry is the constant $2(\nu_c + \rho_c)$ times $p$, with $\rho = (1,0,-1)$, and whose entry at $c \neq d$ is $-\bigl(x_{\max(c,d)}\,\partial_{\min(c,d)}p - x_{\min(c,d)}\,\partial_{\max(c,d)}p\bigr)$. Second, the scalar contraction $$\mathrm{lower}_1(M) = \sum_{a,b,c,d} \frac{(a-c)(c-d)(d-a)}{2}\; x_c\,\partial_b\partial_d\,M_{ab},$$ the indices of $\mathrm{Fin}\,3$ being read as the complex numbers $0,1,2$, so that the weight is the Levi-Civita symbol $\varepsilon_{acd}$. The conclusion is the conjunction of two assertions about $q = \mathrm{lower}_1(\Xi(\nu,p))$: that $q$ is homogeneous of degree $\ell - 1$, truncated natural subtraction (so degree $0$ when $\ell = 0$), and that $q$ is again harmonic, $\sum_{i<3}\partial_i\partial_i q = 0$.
--
--   The matrix $\Xi(\nu,p)$ and the Levi-Civita contraction $\mathrm{lower}_1$ belong to the compact picture of the induced representation $\mathrm{Ind}_B(\nu)$ of $GL_3(\mathbb{R})$, where harmonic homogeneous polynomials in three variables model the $O(3)$-types; the statement says that this degree-lowering operation stays inside that class, shifting the degree down by one. It is used in the construction of transition-stable families, namely by [`LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule) and [`LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (lower₁ (Ξ ν p)).IsHomogeneous (ℓ - 1) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower₁ (Ξ ν p)))) = 0 := by sorry
