-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two
-- name    : LanglandsTunnell.CubicInduction.compactPicture_bottom_mem_of_transitionStable_degree_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/37c6a43e-b888-5874-91d5-a026744a6fd7
-- title:
--   Transition-stable subspaces contain the bottom K-type generator
-- statement:
--   Let $\tau,\tau_3\in\mathbb R$. Define, for $\nu\in\mathbb C^3$ and $p\in\mathbb C[x_0,x_1,x_2]$, the symmetric $3\times 3$ matrix of polynomials $\Xi_\nu p$ whose diagonal entry at $c$ is $2(\nu_c+\rho_c)\,p$ with $\rho=(1,0,-1)$, and whose entry at $(c,d)$ with $c\neq d$ is $x_{\min(c,d)}\partial_{\max(c,d)}p-x_{\max(c,d)}\partial_{\min(c,d)}p$; and define the three linear maps $\mathrm{lower}_2 M=\sum_{c,d}\partial_c\partial_d M_{cd}$, $\mathrm{lower}_1 M=\sum_{a,b,c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\,\partial_b\partial_d M_{ab}$ (indices read as the integers $0,1,2$), and $\mathrm{same}_2 M=6Q-(\sum_i x_i^2)\,\Delta Q$ where $Q=\sum_{c,d}x_c\partial_d M_{cd}$ and $\Delta=\sum_i\partial_i^2$. Put $\nu_{12}=(-\tfrac12+i\tau,\tfrac12+i\tau,i\tau_3)$ and $\nu_{13}=(-\tfrac12+i\tau,i\tau_3,\tfrac12+i\tau)$. The assertion is the conjunction of four statements. For $\nu\in\{\nu_{12},\nu_{13}\}$: whenever $\mathbb C$-subspaces $S_0\le\mathbb C\cdot 1$ and $S_2\le\operatorname{span}\{x_0^2-x_2^2,\;x_1^2-x_2^2\}$ satisfy $\mathrm{lower}_2(\Xi_\nu p)\in S_0$ and $\mathrm{same}_2(\Xi_\nu p)\in S_2$ for all $p\in S_2$, and at least one of $S_0,S_2$ is nonzero, then $1\in S_0$. Moreover: whenever $S_1\le\mathbb C x_2$ and $S_2\le\mathbb C\,x_0x_1$ satisfy $\mathrm{lower}_1(\Xi_{\nu_{12}}p)\in S_1$ for all $p\in S_2$ and are not both zero, then $x_2\in S_1$; and whenever $S_1\le\mathbb C x_1$ and $S_2\le\mathbb C\,x_0x_2$ satisfy $\mathrm{lower}_1(\Xi_{\nu_{13}}p)\in S_1$ for all $p\in S_2$ and are not both zero, then $x_1\in S_1$.
--
--   In the compact picture of a principal series of $\mathrm{GL}_3(\mathbb R)$, isotypic components are modelled by harmonic polynomials in three variables and the action of the Lie algebra by the matrix $\Xi_\nu$ together with the projections $\mathrm{lower}_2$, $\mathrm{lower}_1$, $\mathrm{same}_2$; the statement says that at the half-integral spectral parameters $\nu_{12}$, $\nu_{13}$ a nonzero family of subspaces stable under the relevant transitions must already contain the generator of the lowest component of its sign class. It is used by [`LanglandsTunnell.CubicInduction.compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot`](thm.html#LanglandsTunnell.CubicInduction.compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot), which concludes that such a family vanishes identically once that bottom component is zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Span.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.compactPicture_bottom_mem_of_transitionStable_degree_le_two
    (τ τ₃ : ℝ) :
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
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₂ p) ∈ S₀ ∧ same₂ (Ξ ν₁₂ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₂ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ S₁) ∧
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₃ p) ∈ S₀ ∧ same₂ (Ξ ν₁₃ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₃ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ S₁) := by sorry
