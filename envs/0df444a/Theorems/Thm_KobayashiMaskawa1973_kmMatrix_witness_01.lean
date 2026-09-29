-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_01
-- name    : KobayashiMaskawa1973.kmMatrix_witness_01
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:59:19.482987+00:00
-- url     : https://prove2.me/theorems/0858099e-fd8b-46c3-92dd-2efe5343f9e4
-- title:
--   Witness KM matrix entry (0,1)
-- statement:
--   At $\theta_1=\theta_3=\pi/4$, the (0,1) entry of `kmMatrix` is $-1/2$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_01 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1 = -1/2 := by sorry

end KobayashiMaskawa1973
