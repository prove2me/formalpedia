-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_quartet_im_ne_zero
-- name    : KobayashiMaskawa1973.kmMatrix_witness_quartet_im_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:16:59.53595+00:00
-- url     : https://prove2.me/theorems/fc6def94-7c2e-4ea3-87eb-4eee2d4b1a44
-- title:
--   Witness KM matrix has non-vanishing quartet imaginary part
-- statement:
--   For the explicit parameter values $\theta_1 = \theta_2 = \theta_3 = \pi/4$ and $\delta = \pi/2$, the Kobayashi--Maskawa matrix $K$ satisfies:
--
--   $$\operatorname{Im}(K_{00} K_{11} K_{01}^* K_{10}^*) = \frac{1}{8\sqrt{2}} \neq 0.$$
--
--   Evaluating the definition of `kmMatrix` gives $K_{00} = 1/\sqrt{2}$, $K_{01} = -1/2$, $K_{10} = 1/2$, and $K_{11} = 1/(2\sqrt{2}) - i/2$, so the product is $-1/16 + i/(8\sqrt{2})$, which has non-zero imaginary part.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_quartet_im_ne_zero :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im ≠ 0 := by sorry

end KobayashiMaskawa1973
