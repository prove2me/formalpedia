-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_eq_6
-- name    : LoockCVQEC.RepCode.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:07.556022+00:00
-- url     : https://prove2.me/theorems/7dda2b0a-b825-4873-91aa-af9fada36e37
-- title:
--   Eq. (6) — the tritter-encoded three-mode Wigner function in closed form
-- statement:
--   Let $W_{\mathrm{in}}$ be the coherent state with mean $(\bar x_1,\bar p_1)$ and let the two ancillas be x-squeezed vacua with squeezing parameter $r$. After the tritter, the three-mode state has the Wigner function
--   $$W_{\mathrm{enc}}(x,p)=\Big(\frac2\pi\Big)^3\exp\Big\{-2\Big[\tfrac1{\sqrt3}(x_1+x_2+x_3)-\bar x_1\Big]^2-\tfrac23e^{-2r}\big[(p_1-p_2)^2+(p_2-p_3)^2+(p_1-p_3)^2\big]-2\Big[\tfrac1{\sqrt3}(p_1+p_2+p_3)-\bar p_1\Big]^2-\tfrac23e^{2r}\big[(x_1-x_2)^2+(x_2-x_3)^2+(x_1-x_3)^2\big]\Big\}$$
--   for all $x,p\in\mathbb R^3$.
--
--   The encoded state is an entangled three-mode Gaussian state: the signal's mean is spread evenly over the three modes, and the ancillas' squeezing correlates the $x$-quadratures of all three.
--
--   **Formalization Note** The left-hand side is computed from the protocol: the product state (5) evaluated at $(Dx,Dp)$, with Lean index $0$ for the paper's mode 1.
--
--   Differences from the source:
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
--   - reading: the tritter is "a sequence of two beam splitters with transmittances 1 : 2 and 1 : 1"; its matrix is not printed → the orthogonal matrix D with rows (1,1,1)/√3, (√(2/3), −1/√6, −1/√6), (0, 1/√2, −1/√2); encode W ↦ W(Dx, Dp), decode W ↦ W(Dᵀx, Dᵀp); reason: this D reproduces Eq. (6) and every term, with signs, of Eq. (8) on the page
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 2, Eq. (6)

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real

theorem eq_6 (xb pb r : ℝ) (x p : Fin 3 → ℝ) :
    encode (prodW xb pb r) x p =
      (2 / π) ^ 3 * exp (-2 * (1 / √3 * (x 0 + x 1 + x 2) - xb) ^ 2
        - 2 / 3 * exp (-2 * r) * ((p 0 - p 1) ^ 2 + (p 1 - p 2) ^ 2 + (p 0 - p 2) ^ 2)
        - 2 * (1 / √3 * (p 0 + p 1 + p 2) - pb) ^ 2
        - 2 / 3 * exp (2 * r) * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 0 - x 2) ^ 2)) := by sorry

end LoockCVQEC.RepCode
