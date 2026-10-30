-- Prove2me | Theorems.Thm_HolevoCQ_sqrt_gram_ineq
-- name    : HolevoCQ.sqrt_gram_ineq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:56.89191+00:00
-- url     : https://prove2.me/theorems/c5542725-a98c-4bb0-b0be-6d78fb669afe
-- title:
--   §5 (in (16)): $(E-\Gamma^{1/2})^2=(E-\Gamma)^2(E+\Gamma^{1/2})^{-2}\le(E-\Gamma)^2$
-- statement:
--   Let $\Gamma$ be a positive semidefinite matrix and $E$ the unit matrix. Then
--
--   $$
--   (E-\Gamma^{1/2})^2=(E-\Gamma)^2(E+\Gamma^{1/2})^{-2}\le(E-\Gamma)^2 ,
--   $$
--
--   where $E+\Gamma^{1/2}$ is invertible because $\Gamma^{1/2}\ge0$. In the paper $\Gamma$ is the Gram matrix of the projected eigenvectors $P|e^u_J\rangle$, and the inequality is the step that turns the error bound (15) into a bound in terms of $\Gamma$ itself.
--
--   Differences from the source:
--   - generalization: $\Gamma$ the Gram matrix $[\gamma_{(u,J),(u',J')}]$ of (14) → any positive semidefinite matrix on a finite index type; reason: every Gram matrix is positive semidefinite, and positivity is the only property the step uses
--   - encoding: matrix inequality $\le$ and $(E+\Gamma^{1/2})^{-2}$ → positive semidefiniteness of the difference; the square of the matrix inverse; $\Gamma^{1/2}$ as `cfc Real.sqrt Γ`; reason: Lean convention; $E+\Gamma^{1/2}$ is invertible, so the inverse is the true inverse
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §5, in eq. (16), p.5

import Mathlib

open scoped ComplexOrder

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §5, p.5 (in (16)): for the (positive) Gram matrix `Γ` and the unit
matrix `E`, `(E − Γ^{1/2})² = (E − Γ)² (E + Γ^{1/2})^{−2} ≤ (E − Γ)²`.

**Formalization Note.** Stated for every positive semidefinite `Γ` on a finite index type (the
only property of the Gram matrix used). `Γ^{1/2}` is `cfc Real.sqrt Γ`; `(E + Γ^{1/2})^{−2}` is
the square of the matrix inverse, and `E + Γ^{1/2}` is invertible. The order `A ≤ B` is
`(B - A).PosSemidef`. -/
theorem sqrt_gram_ineq {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ)
    (hΓ : Γ.PosSemidef) :
    (1 - cfc Real.sqrt Γ) ^ 2 = (1 - Γ) ^ 2 * ((1 + cfc Real.sqrt Γ)⁻¹) ^ 2 ∧
      ((1 - Γ) ^ 2 - (1 - cfc Real.sqrt Γ) ^ 2).PosSemidef := by sorry

end HolevoCQ
