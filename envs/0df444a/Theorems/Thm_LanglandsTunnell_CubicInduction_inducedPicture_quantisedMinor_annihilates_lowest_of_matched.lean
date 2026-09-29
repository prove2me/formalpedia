-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched
-- name    : LanglandsTunnell.CubicInduction.inducedPicture_quantisedMinor_annihilates_lowest_of_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/6b9172b3-af94-5246-90f2-0c420d477916
-- title:
--   Quadratic operator annihilating constants and one row in the induced picture
-- statement:
--   Fix real numbers $\tau,\tau_3$. Polynomials in $\mathbb{C}[X_{(a,b)} : (a,b)\in \mathrm{Fin}\,3\times\mathrm{Fin}\,3]$ are thought of as functions of the nine entries of a $3\times 3$ matrix. For a vector $\nu : \mathrm{Fin}\,3\to\mathbb{C}$ and indices $c,d$, the operator $\mathrm{act}_\nu(c,d)$ sends $p$ to $\bigl(\sum_a (\nu_a+\rho_a)\,X_{(a,c)}X_{(a,d)}\bigr)p+\sum_{i,j}\bigl(\sum_m \kappa_{im}X_{(m,j)}\bigr)\,\partial p/\partial X_{(i,j)}$, where $\rho=(1,0,-1)$ and $\kappa$ is the antisymmetric matrix with $\kappa_{im}=X_{(i,c)}X_{(m,d)}$ for $m<i$, $\kappa_{im}=-X_{(m,c)}X_{(i,d)}$ for $i<m$, and $\kappa_{ii}=0$; thus the first-order part is the product $\kappa X$. For $c'\in\mathbb{C}$ put $\delta_\nu(c')f=\mathrm{act}_\nu(0,1)\bigl(\mathrm{act}_\nu(1,2)f\bigr)-\mathrm{act}_\nu(0,2)\bigl(\mathrm{act}_\nu(1,1)f\bigr)-c'\,\mathrm{act}_\nu(0,2)f$. Let $\nu_{12}=(-\tfrac12+i\tau,\ \tfrac12+i\tau,\ i\tau_3)$, $\nu_{13}=(-\tfrac12+i\tau,\ i\tau_3,\ \tfrac12+i\tau)$ and $c'=\tfrac12-i\tau$. Call $k:\mathrm{Fin}\,3\times\mathrm{Fin}\,3\to\mathbb{C}$ orthogonal when $\sum_a k_{ia}k_{ja}=\delta_{ij}$ for all $i,j$. The assertion is that for every such $k$: $\delta_{\nu_{12}}(c')(1)$ evaluates to $0$ at $k$; $\delta_{\nu_{12}}(c')(X_{(2,j)})$ evaluates to $0$ at $k$ for every $j$; $\delta_{\nu_{13}}(c')(1)$ evaluates to $0$ at $k$; and $\delta_{\nu_{13}}(c')(X_{(1,j)})$ evaluates to $0$ at $k$ for every $j$.
--
--   This is an explicit computation in the induced (compact-picture) model of a principal series of $\mathrm{GL}_3(\mathbb{R})$ at the two half-integral spectral parameters $\nu_{12},\nu_{13}$: a specific quadratic element of the enveloping algebra kills the constant vector and the three coordinate functions of one distinguished row, on the orthogonal matrices. It feeds the argument that a suitable submodule is stable and separating, used by [`LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.inducedPicture_quantisedMinor_annihilates_lowest_of_matched
    (τ τ₃ : ℝ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let δ : (Fin 3 → ℂ) → ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c' f => act ν 0 1 (act ν 1 2 f) - act ν 0 2 (act ν 1 1 f) - MvPolynomial.C c' * act ν 0 2 f
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    let c' : ℂ := 1 / 2 - τ * Complex.I
    let IsOrthogonal : (Fin 3 × Fin 3 → ℂ) → Prop :=
      fun k => ∀ i j : Fin 3, ∑ a : Fin 3, k (i, a) * k (j, a) = if i = j then 1 else 0
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k →
      MvPolynomial.eval k (δ ν₁₂ c' (1 : MvPolynomial (Fin 3 × Fin 3) ℂ)) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k → ∀ j : Fin 3,
      MvPolynomial.eval k (δ ν₁₂ c' (MvPolynomial.X (2, j))) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k →
      MvPolynomial.eval k (δ ν₁₃ c' (1 : MvPolynomial (Fin 3 × Fin 3) ℂ)) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k → ∀ j : Fin 3,
      MvPolynomial.eval k (δ ν₁₃ c' (MvPolynomial.X (1, j))) = 0) := by sorry
