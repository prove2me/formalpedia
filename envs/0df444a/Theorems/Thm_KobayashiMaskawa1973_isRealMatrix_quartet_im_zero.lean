-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_isRealMatrix_quartet_im_zero
-- name    : KobayashiMaskawa1973.isRealMatrix_quartet_im_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:17:19.699885+00:00
-- url     : https://prove2.me/theorems/5285f246-6c1f-4e1c-aea6-9ff08708cc8b
-- title:
--   Real matrix has vanishing imaginary part for quartet product
-- statement:
--   If a complex matrix $V \in \mathrm{M}_3(\mathbb{C})$ is real in the sense of `IsRealMatrix V` (every entry has vanishing imaginary part: $\forall i j, \operatorname{Im}(V_{ij}) = 0$), then the quartet product has vanishing imaginary part:
--
--   $$\operatorname{Im}(V_{00} V_{11} V_{01}^* V_{10}^*) = 0.$$
--
--   Since each entry is real, the complex conjugate satisfies $V_{ij}^* = V_{ij} \in \mathbb{R}$, and the product of four real numbers is real.
-- source:
--   Definitions.Def_KobayashiMaskawa1973_Defs

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem isRealMatrix_quartet_im_zero (V : Matrix (Fin 3) (Fin 3) ℂ) (h : IsRealMatrix V) :
    (V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0)).im = 0 := by sorry

end KobayashiMaskawa1973
