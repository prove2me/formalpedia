-- Prove2me | Theorems.Thm_MasulloRH_cell_operator_product_and_winding_reconstruction
-- name    : MasulloRH.cell_operator_product_and_winding_reconstruction
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T20:25:22.701089+00:00
-- url     : https://prove2.me/theorems/b07affbd-42a1-483c-b695-0127ef211b1c
-- title:
--   Recover winding operators from the diagonal blocks and first input column of an actual bounded-operator product
-- statement:
--   In a complex inner-product space let P be the orthogonal projection onto a subspace admitting one. For 0<r<1, a unit phase u and a sequence F of bounded cell operators, set q=r², a=r conj(u), b=r u. The normalized cell train with coefficients sqrt(1−r²)a^m preserves squared norms and has Gram coefficients (1−q)a^m b^n. Form E(m,n) from these coefficients multiplying I−P, subtracting I only at (0,0). Form the lower triangular product blocks K(i,j) by summing the actual compositions F(i−m) E(m,j) for 0≤m≤i. The theorem recovers F(0) from the diagonal block K(0,0) using an explicit two-sided inverse and recovers every b^j F(j) from two consecutive diagonal blocks, the first-column composition K(j,0)P and the recovered zeroth block. It verifies the special correction at j=1, the sign of the first-column contribution, and the resulting finite sums of all windings. Taking P=0 gives the pole-free case; taking P to be the projection onto the cell pole line gives the principal case.
-- source:
--   Masullo mission, full two-variable cell reconstruction in the global matched Hardy chart. This theorem verifies the normalized geometric train and noncommutative bounded-operator product algebra. The analytic identification with global projection blocks, the explicit integral kernels, and the log-circle change of metric are separate paper arguments. Related accepted endpoint scalar derivative theorem d1377673-b704-441b-b69b-f445ee5f8275.

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ComplexConjugate

theorem MasulloRH.cell_operator_product_and_winding_reconstruction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (F : ℕ → H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (hr' : r < 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    let a := (r:ℂ) * (starRingEnd ℂ) u
    let b := (r:ℂ) * u
    let q := ((r^2 : ℝ) : ℂ)
    let train := fun m : ℕ => ((Real.sqrt (1-r^2):ℝ):ℂ)*a^m
    let P := W.starProjection
    let E := fun m n : ℕ => ((1-q)*a^m*b^n) • (1-P) -
      (if m=0 ∧ n=0 then 1 else 0)
    let K := fun i j : ℕ => ∑ m ∈ Finset.range (i+1), F (i-m) * E m j
    let T := fun j => K j j
    let N : H →L[ℂ] H := q • 1 + (1-q) • P
    let S : H →L[ℂ] H := q⁻¹ • (1-P) + P
    let Z := -(T 0 * S)
    let G := fun n : ℕ => (1-q)⁻¹ •
      (T (n+1) - q • T n - (if n=0 then q • Z else 0)) -
      b^(n+1) • (K (n+1) 0 * P)
    (∀ x : H, HasSum (fun m : ℕ => ‖train m • x‖^2) (‖x‖^2)) ∧
    (∀ m n, train m * (starRingEnd ℂ) (train n) = (1-q)*a^m*b^n) ∧
    N*S=1 ∧ S*N=1 ∧ Z=F 0 ∧
    (∀ j, K j 0 * P = -(F j * P)) ∧
    (∀ n : ℕ, T (n+1) - q • T n - (if n=0 then q • Z else 0) =
      ((1-q)*b^(n+1)) • (F (n+1)*(1-P))) ∧
    (∀ n : ℕ, G n = b^(n+1) • F (n+1)) ∧
    ∀ M : ℕ, Z + ∑ n ∈ Finset.range M, G n =
      F 0 + ∑ n ∈ Finset.range M, b^(n+1) • F (n+1) := by sorry
