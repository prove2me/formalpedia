-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_entries
-- name    : KobayashiMaskawa1973.kmMatrix_witness_entries
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:47:10.943607+00:00
-- url     : https://prove2.me/theorems/a18852f1-784a-413d-9b9c-a15eaf17ab0c
-- title:
--   Entries of the witness KM matrix
-- statement:
--   Evaluating `kmMatrix` at $\theta_1 = \theta_2 = \theta_3 = \pi/4$ and $\delta = \pi/2$ gives:
--
--   $$K_{00} = \frac{1}{\sqrt{2}}, \quad K_{01} = -\frac{1}{2}, \quad K_{10} = \frac{1}{2}, \quad K_{11} = \frac{1}{2\sqrt{2}} - \frac{i}{2}.$$
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_entries :
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ)) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1 = -1/2) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0 = 1/2) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1 = (1 / (2 * Real.sqrt 2) - Complex.I / 2)) := by sorry

end KobayashiMaskawa1973
