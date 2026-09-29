-- Prove2me | Theorems.Thm_MTT_period_vanishing
-- name    : MTT.period_vanishing
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T16:49:19.893504+00:00
-- url     : https://prove2.me/theorems/12542542-b0fc-4959-b734-052b70cdacbc
-- title:
--   A cusp form with vanishing period integrals is zero
-- statement:
--   If every modular integral of a weight-k cusp form against X^j vanishes, for all degrees j from 0 to k-2 and every rational base point r, then the cusp form is zero. Equivalently, the period integrals along the vertical rays from the rational cusps to i-infinity, taken with all polynomial weights of degree at most k-2, separate cusp forms. This is the injectivity half of the Eichler-Shimura correspondence. It is not a formal consequence of Hecke equivariance or of multiplicity one, both of which constrain the image of the period map rather than its kernel.
--
--   Formalization note. Expanding the q-expansion under the integral is not by itself a proof. On a vertical ray truncated at height T > 0 the interchange is legitimate and produces the series with n-th term a_n e(nr) e^{-2 pi n T} / (2 pi n), but letting T tend to 0 is an Abel limit rather than a convergent sum: the Hecke bound only gives a_n = O(n^{k/2}), so the coefficients a_n / n need not be summable, and the resulting function of r is not continuous. A proof has to control the period map itself, not merely its formal Fourier expansion.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), Theorem 2.3

import Definitions.Def_MTT_Arithmetic
set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem MTT.period_vanishing
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (h : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
      MTT.modularIntegral f (Polynomial.X ^ j) r = 0) :
    f = 0 := by sorry
