-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_11
-- name    : KobayashiMaskawa1973.kmMatrix_witness_11
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:59:39.307534+00:00
-- url     : https://prove2.me/theorems/28296c76-aa25-4740-8471-cd8747734cdf
-- title:
--   Witness KM matrix entry (1,1)
-- statement:
--   At $\theta_1=\theta_2=\theta_3=\pi/4$ and $\delta=\pi/2$, the (1,1) entry of `kmMatrix` is $1/(2\sqrt{2}) - i/2$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_11 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1 = (1 / (2 * Real.sqrt 2) - Complex.I / 2) := by sorry

end KobayashiMaskawa1973
