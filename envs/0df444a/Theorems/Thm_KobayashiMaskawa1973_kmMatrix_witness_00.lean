-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_00
-- name    : KobayashiMaskawa1973.kmMatrix_witness_00
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:59:11.080366+00:00
-- url     : https://prove2.me/theorems/fbfb6379-ef56-4953-9bb0-a877902070dc
-- title:
--   Witness KM matrix entry (0,0)
-- statement:
--   At $\theta_1=\pi/4$, the (0,0) entry of `kmMatrix` is $1/\sqrt{2}$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_00 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ) := by sorry

end KobayashiMaskawa1973
