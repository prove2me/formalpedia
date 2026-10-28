-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_interval_majorant
-- name    : HlawkaSchatten.DiagonalCutoff4.ordered_interval_majorant
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T00:45:32.317089+00:00
-- url     : https://prove2.me/theorems/2e96402f-d6fe-4683-9762-4b654066b25a
-- title:
--   Three-vertex norm bound retaining both lower and upper tail bounds
-- statement:
--   Let $p\ge1$ and $l<h$. Suppose the affine function $c+\alpha u+\beta v$ bounds $\|(1,u,v)\|_p$ at each of the three points $(l,l)$, $(h,l)$, and $(h,h)$. Then
--   $$\|(1,u,v)\|_p\le c+\alpha u+\beta v\qquad(l\le v\le u\le h).$$
--   All parameters are real. No sign restrictions on the affine coefficients or on $l,h$ are required. This strengthens the ordered-tail localization tool by retaining a lower tail bound.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Data.Fin.VecNotation
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.ordered_interval_majorant {p lo hi c alpha beta u v : ℝ}
    (hp : 1 ≤ p) (hlohi : lo < hi)
    (h00 : lpNorm p ![1,lo,lo] ≤ c+alpha*lo+beta*lo)
    (h10 : lpNorm p ![1,hi,lo] ≤ c+alpha*hi+beta*lo)
    (h11 : lpNorm p ![1,hi,hi] ≤ c+alpha*hi+beta*hi)
    (hlov : lo ≤ v) (hvu : v ≤ u) (huhi : u ≤ hi) :
    lpNorm p ![1,u,v] ≤ c+alpha*u+beta*v := by sorry
