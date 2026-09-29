-- Prove2me | Theorems.Thm_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
-- name    : Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b47d02bc-edea-5cd3-adea-50a6420de447
-- title:
--   Trace identity forces a relation between det(1-XM) and the Eᵢ
-- statement:
--   Let $K$ be a field of characteristic zero and let $M$ be a square matrix over $K$ indexed by a finite type $m$. Let $k$ be a natural number, let $E : \mathrm{Fin}\,k \to K[X]$ be a family of polynomials each of which has constant coefficient $1$, and let $a : \mathrm{Fin}\,k \to \mathbb{Z}$ be a family of integers. Assume that for every integer $j \ge 1$ the trace of $M^{j}$ equals $\sum_{i} a_i \cdot c_j(i)$, where $a_i$ is viewed in $K$ through the canonical ring map and $c_j(i)$ is the coefficient of $X^{j}$ in the formal power series $\bigl(-X\,E_i'\bigr)\cdot E_i^{-1}$, the product of the image in $K[[X]]$ of the polynomial $-X \cdot \mathrm{d}E_i/\mathrm{d}X$ with the power-series inverse of the image of $E_i$ (which exists since $E_i$ has unit constant term). The conclusion is the identity in $K[X]$
--   $$\mathrm{charpolyRev}(M)\cdot\prod_{i} E_i^{\,(-a_i)^{+}} \;=\; \prod_{i} E_i^{\,a_i^{+}},$$
--   where $\mathrm{charpolyRev}(M)$ is the reversed characteristic polynomial $\det(1 - X\,M)$ and $n^{+}$ denotes the truncation of an integer $n$ to a natural number, so that the negatively indexed $E_i$ contribute on the left and the positively indexed ones on the right.
--
--   This is the linear-algebra core of Artin's formalism for $L$-series: matching power-trace data against logarithmic derivatives $-XE'/E$ of polynomials with constant term $1$ determines $\det(1-XM)$ up to the prescribed products of the $E_i$. It is used to pass from a character identity to the corresponding identity of Euler factors, and is cited by [`ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
    {K : Type*} [Field K] [CharZero K] {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m K) {k : ℕ} (E : Fin k → Polynomial K) (hE : ∀ i, (E i).coeff 0 = 1)
    (a : Fin k → ℤ)
    (h : ∀ j : ℕ, 0 < j → (M ^ j).trace =
      ∑ i, (a i : K) * PowerSeries.coeff j
        (((-(Polynomial.X * Polynomial.derivative (E i)) : Polynomial K) : PowerSeries K) *
          ((E i : Polynomial K) : PowerSeries K)⁻¹)) :
    M.charpolyRev * ∏ i, E i ^ (-a i).toNat = ∏ i, E i ^ (a i).toNat := by sorry
