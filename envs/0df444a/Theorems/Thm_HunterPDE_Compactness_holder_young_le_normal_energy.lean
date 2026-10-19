-- Prove2me | Theorems.Thm_HunterPDE_Compactness_holder_young_le_normal_energy
-- name    : HunterPDE.Compactness.holder_young_le_normal_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T13:49:45.379212+00:00
-- url     : https://prove2.me/theorems/cf42104b-5032-4e4e-adea-6854e31031f8
-- title:
--   Anisotropic Young inequality: Holder product of energies bounded by the sum
-- statement:
--   This is Young's inequality in the anisotropic form used to pass from the Holder product of two energies to the sum of those energies, with the constant $p$ kept explicit.
--
--   Let $1\le p<\infty$ and let $A,B\in[0,\infty]$ be arbitrary extended nonnegative real numbers. Then
--
--   $$p\,A^{\frac{p-1}{p}}\,B^{\frac1p}\le p\,(A+B).$$
--
--   Both factors of the Holder product are weighted by the complementary exponents $\frac{p-1}{p}$ and $\frac1p$, which sum to $1$, so the weighted arithmetic-geometric mean inequality applies. The inequality is insensitive to whether $A$ or $B$ is infinite, and it covers the endpoint $p=1$, where the zero-order factor has exponent $0$.
--
--   **Formalization Note** $A$ and $B$ are extended nonnegative reals and the powers are `ENNReal.rpow` with real exponents; the constant is `ENNReal.ofReal p.toReal`.
-- source:
--   Standard weighted Young (arithmetic-geometric mean) inequality, in the anisotropic form used in the proof of J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed p. 72.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.holder_young_le_normal_energy (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (A B : ℝ≥0∞) :
    ENNReal.ofReal p.toReal * A ^ ((p.toReal - 1) / p.toReal) * B ^ (1 / p.toReal) ≤
      ENNReal.ofReal p.toReal * (A + B) := by sorry
