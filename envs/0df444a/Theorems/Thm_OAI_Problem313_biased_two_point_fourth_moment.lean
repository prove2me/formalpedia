-- Prove2me | Theorems.Thm_OAI_Problem313_biased_two_point_fourth_moment
-- name    : OAI.Problem313.biased_two_point_fourth_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:49:50.263991+00:00
-- url     : https://prove2.me/theorems/bfbe11b8-9761-46b9-97d1-86f47fb7062e
-- title:
--   A two-point fourth-moment inequality for biased bits
-- statement:
--   For $0\le p\le1$ and all real $a,b$,
--   $$
--   (1-p)\Bigl(a-\frac{pb}4\Bigr)^4+p\Bigl(a+\frac{(1-p)b}4\Bigr)^4\le(a^2+b^2)^2 .
--   $$
--
--   This is the one-coordinate case of a $(2,4)$-hypercontractive inequality for the $p$-biased noise operator with parameter $\sqrt{p(1-p)}/4$; the two values $-p/4$ and $(1-p)/4$ come from the normalized character. Tensorizing it bounds fourth moments of low-degree functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/TwoPoint.lean#L14-L35

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

open OAI OAI.Problem313

theorem OAI.Problem313.biased_two_point_fourth_moment (p a b : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (a - p * b / 4) ^ 4 + p * (a + (1 - p) * b / 4) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by sorry
