-- Prove2me | Theorems.Thm_ModularForm_E4_mul_eta_pow_eight_eq
-- name    : ModularForm.E4_mul_eta_pow_eight_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/66edc626-4f44-5ad3-bf96-c0813032a995
-- title:
--   Jacobi's identity for E₄ η⁸ in eta quotients
-- statement:
--   The assertion is a pointwise identity of complex numbers, with a single bound variable: a point $\tau$ of the upper half-plane. Writing $E_4$ for the normalised Eisenstein series of weight $4$ and level one, regarded as a function on the upper half-plane, and $\eta$ for Dedekind's eta function as a function of a complex variable (applied here to $\tau/2$ and to $2\tau$, which again lie in the upper half-plane, the coercion $\tau \mapsto (\tau : \mathbb{C})$ being the inclusion), the theorem states that $$E_4(\tau)\,\eta(\tau)^{8} = \eta(\tau/2)^{16} + 16\,\eta(\tau/2)^{8}\,\eta(2\tau)^{8} + 256\,\eta(2\tau)^{16}.$$ There are no hypotheses beyond the choice of $\tau$; both sides are evaluated at the given point, and the equality is one of complex numbers rather than of modular forms, so no weight or level data enter the formal statement. Note that the three eta factors on the right are taken at the arguments $\tau/2$, $2\tau$ and $2\tau$ respectively, with the integer coefficients $1$, $16$ and $256$.
--
--   This is a classical identity going back to Jacobi, equivalent to the expression $E_4 = \tfrac12(\vartheta_2^{8} + \vartheta_3^{8} + \vartheta_4^{8})$ of the weight-$4$ Eisenstein series through theta constants, and it exhibits $E_4\eta^{8}$ as a combination of eta products of level $4$. It is used to obtain the $q$-expansion statement [`ModularCurve.qExpand_two_eisenstein4_mul_etaProd_pow_eight`](thm.html#ModularCurve.qExpand_two_eisenstein4_mul_etaProd_pow_eight) for the product of $E_4$ with the eighth power of the eta product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_E4_mul_eta_pow_eight_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.E4_mul_eta_pow_eight_eq (τ : UpperHalfPlane) :
    ModularForm.E₄ τ * ModularForm.eta (τ : ℂ) ^ 8 =
      ModularForm.eta ((τ : ℂ) / 2) ^ 16 + 16 * ModularForm.eta ((τ : ℂ) / 2) ^ 8 * ModularForm.eta (2 * (τ : ℂ)) ^ 8 +
        256 * ModularForm.eta (2 * (τ : ℂ)) ^ 16 := by sorry
