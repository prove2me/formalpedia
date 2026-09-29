-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_quartet_im_eq
-- name    : KobayashiMaskawa1973.kmMatrix_witness_quartet_im_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:29:00.369368+00:00
-- url     : https://prove2.me/theorems/f8b8014b-8e7c-4f49-9e11-839421662887
-- title:
--   Imaginary part of witness KM quartet equals 1 / (8 * sqrt 2)
-- statement:
--   Evaluating the definition of `kmMatrix` at $\theta_1 = \theta_2 = \theta_3 = \pi/4$ and $\delta = \pi/2$, the imaginary part of the plaquette quartet product is exactly:
--
--   $$\operatorname{Im}(K_{00} K_{11} K_{01}^* K_{10}^*) = \frac{1}{8\sqrt{2}}.$$
--
--   This follows from $\cos(\pi/4) = \sin(\pi/4) = 1/\sqrt{2}$ and $e^{i\pi/2} = i$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_witness_quartet_im_eq :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im = 1 / (8 * Real.sqrt 2) := by sorry

end KobayashiMaskawa1973
