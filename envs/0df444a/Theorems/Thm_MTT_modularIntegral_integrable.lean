-- Prove2me | Theorems.Thm_MTT_modularIntegral_integrable
-- name    : MTT.modularIntegral_integrable
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T04:33:14.913436+00:00
-- url     : https://prove2.me/theorems/e84c779e-52f4-48ee-8722-0e8df68a2522
-- title:
--   The modular-integral integrand is integrable on the vertical ray
-- statement:
--   For a cusp form f of weight k and level N, an arbitrary polynomial P, and a rational base point r, the function t maps to f(r + it) P(r + it) is integrable over the open half line t > 0. This is what makes the modular integral of Mazur-Tate-Teitelbaum a genuine Lebesgue integral rather than a formal symbol, and it is the hypothesis needed to know that the modular integral is additive in f.
--
--   Two separate decay statements are involved. As t tends to infinity the cusp form is exponentially small because its q-expansion at the cusp at infinity has no constant term, and this dominates the polynomial growth of P. As t tends to zero the vertical ray approaches the rational point r, which is a cusp of Gamma_1(N); the cusp form vanishes there as well, again exponentially in 1/t after passing to the local parameter. The second statement is the substantive one: the Petersson bound alone gives only |f(r+it)| = O(t^{-k/2}), which is not integrable near zero for k at least 2, so a genuine expansion at the cusp r is required.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), Theorem 2.3 and §4

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.modularIntegral_integrable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
        P.eval ((r : ℂ) + Complex.I * t))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by sorry
