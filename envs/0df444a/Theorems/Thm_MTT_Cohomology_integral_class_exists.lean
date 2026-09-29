-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_class_exists
-- name    : MTT.Cohomology.integral_class_exists
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T04:33:17.545637+00:00
-- url     : https://prove2.me/theorems/c346aaac-d748-4f4f-bc7f-e9c57a8a5697
-- title:
--   The period polynomials of a cusp form assemble into a cohomology class
-- statement:
--   For every weight-k cusp form f of level N there exists a compactly supported cohomology class, with homogeneous binary form coefficients of degree k-2, whose coefficient evaluation on the path from the cusp at infinity to a rational cusp r is binomial(k-2,j) times the modular integral of f against X^j at r, for every j from 0 to k-2.
--
--   Equivalently, the period polynomial of f at r, namely the sum over j of binomial(k-2,j) times the integral of f against X^j at r, times the monomial X^j Y^(k-2-j), is the value at the path from infinity to r of a Gamma_1(N)-equivariant cocycle on pairs of cusps. The cocycle relation itself is automatic once one sets the value on a general path to be the difference of the values at its endpoints; the content of the statement is the Gamma_1(N)-equivariance, which compares the integral of f along a vertical ray with the integral along its image under an element of the group, a circular arc rather than a ray. That comparison is a contour deformation, using holomorphy of the integrand together with the decay of f at the cusps.
--
--   The class is unique when it exists, so this existence statement determines it. Injectivity of the resulting map, and its Hecke equivariance, are separate obligations.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), Theorem 2.3 and §4

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_exists
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    ∃ φ : Hc N (k - 2) ℂ, IntegralClass f φ := by sorry
