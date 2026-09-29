-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
-- name    : LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8a25b1ef-e63c-52d9-9d78-e70bd3d95600
-- title:
--   No harmonic polynomial of degree ≥ 3 in both lowering kernels
-- statement:
--   Fix real numbers $\tau,\tau_3$ and a natural number $\ell$ with $3\le\ell$. Three operators on $3\times 3$ matrices of polynomials in $\mathbb{C}[x_0,x_1,x_2]$ are introduced: for $\nu\colon \mathrm{Fin}\,3\to\mathbb{C}$ and a polynomial $p$, the matrix $\Xi_\nu(p)$ has diagonal entries $2(\nu_c+\rho_c)\,p$ with $\rho=(1,0,-1)$ and, for $c\neq d$, entries $-(x_{\max(c,d)}\partial_{\min(c,d)}p-x_{\min(c,d)}\partial_{\max(c,d)}p)$; $\mathrm{lower}_2(M)=\sum_{c,d}\partial_c\partial_d M_{cd}$; and $\mathrm{lower}_1(M)=\sum_{a,b,c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\,\partial_b\partial_d M_{ab}$, the indices being read as the integers $0,1,2$ mapped into $\mathbb{C}$. A fourth operator $\mathrm{same}_2(M)=6\sum_{c,d}x_c\partial_d M_{cd}-(\sum_i x_i^2)\sum_i\partial_i\partial_i\bigl(\sum_{c,d}x_c\partial_d M_{cd}\bigr)$ is also named but does not occur in the conclusion. Put $\nu_{12}=(-\tfrac12+i\tau,\ \tfrac12+i\tau,\ i\tau_3)$ and $\nu_{13}=(-\tfrac12+i\tau,\ i\tau_3,\ \tfrac12+i\tau)$. The assertion is that for every polynomial $p$ in three complex variables that is homogeneous of degree $\ell$ and harmonic, i.e. $\sum_i\partial_i\partial_i p=0$, and for $\nu$ equal to either $\nu_{12}$ or $\nu_{13}$: if $\mathrm{lower}_2(\Xi_\nu(p))=0$ and $\mathrm{lower}_1(\Xi_\nu(p))=0$, then $p=0$.
--
--   In the model of the isotypic components of a principal series of $\mathrm{GL}_3(\mathbb{R})$ by harmonic homogeneous polynomials in three variables, this says that at the half-integral spectral parameters $\nu_{12},\nu_{13}$ no nonzero harmonic polynomial of degree at least three is annihilated by both degree-lowering transitions; the realness of $\tau,\tau_3$ and the bound $\ell\ge 3$ are both used. It feeds the analysis of transition-stable families of $K$-types used in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
    (τ τ₃ : ℝ) (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 →
      (lower₂ (Ξ ν₁₂ p) = 0 → lower₁ (Ξ ν₁₂ p) = 0 → p = 0) ∧
      (lower₂ (Ξ ν₁₃ p) = 0 → lower₁ (Ξ ν₁₃ p) = 0 → p = 0) := by sorry
