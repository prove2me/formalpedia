-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_complex_quartet_eval
-- name    : KobayashiMaskawa1973.complex_quartet_eval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:58:55.839987+00:00
-- url     : https://prove2.me/theorems/362c9570-97c2-4823-bf03-b4de747b73c3
-- title:
--   Imaginary part evaluation of the witness quartet
-- statement:
--   For any real $s$, the imaginary part of $(1/s)(1/(2s) - i/2) (-1/2)^* (1/2)^*$ equals $1/(8s)$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib

namespace KobayashiMaskawa1973

theorem complex_quartet_eval (s : ℝ) :
    (((1 / s : ℂ) * (1 / (2 * s) - Complex.I / 2) * star (-1/2 : ℂ) * star (1/2 : ℂ))).im = 1 / (8 * s) := by sorry

end KobayashiMaskawa1973
