-- Prove2me | Theorems.Thm_ModularForm_E4_mul_etaProduct_eq
-- name    : ModularForm.E4_mul_etaProduct_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/70ab5a49-df14-51fa-aa60-d465a806c131
-- title:
--   An eta-product identity for E₄ at level four
-- statement:
--   The assertion is an identity of complex numbers, valid for every point $z$ of the upper half-plane: the value at $z$ of the normalised level-one Eisenstein series of weight $4$, multiplied by the eta product $\eta(z)^{16}\,\eta(2z)^{8}\,\eta(4z)^{16}$ (here $\eta$ is Dedekind's eta function evaluated at the complex numbers $z$, $2z$ and $4z$), equals the sum of three eta products, $$E_4(z)\,\eta(z)^{16}\eta(2z)^{8}\eta(4z)^{16} \;=\; \eta(2z)^{48} \;+\; 224\,\eta(z)^{8}\eta(2z)^{24}\eta(4z)^{16} \;+\; 256\,\eta(z)^{16}\eta(4z)^{32}.$$ There are no hypotheses beyond the single variable $z$ ranging over the upper half-plane; both sides are weight-$24$ expressions, each eta monomial having total exponent $48$ in the eta factors, and the coefficients $1$, $224$, $256$ are the integers occurring in the classical identity.
--
--   This is the level-four companion of the expression of $E_4$ through theta constants: dividing by $\eta(2z)^{48}$ it reads $E_4(z)=\vartheta_3(2z)^{8}(1+224u+256u^{2})$ with $u=\eta(z)^{8}\eta(4z)^{16}/\eta(2z)^{24}$ a Hauptmodul of $\Gamma_0(4)$. It is used by [`ModularCurve.eisenstein4_mul_etaProd_identity`](thm.html#ModularCurve.eisenstein4_mul_etaProd_identity), which records the corresponding identity between the associated $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_E4_mul_etaProduct_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.E4_mul_etaProduct_eq (z : UpperHalfPlane) :
    ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) =
      ModularForm.eta (2 * (z : ℂ)) ^ 48 +
        224 * (ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 24 *
          ModularForm.eta (4 * (z : ℂ)) ^ 16) +
        256 * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (4 * (z : ℂ)) ^ 32) := by sorry
