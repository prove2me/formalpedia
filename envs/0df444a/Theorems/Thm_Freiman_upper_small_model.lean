-- Prove2me | Theorems.Thm_Freiman_upper_small_model
-- name    : Freiman.upper_small_model
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:17.937894+00:00
-- url     : https://prove2.me/theorems/9c800aac-a481-4ae4-87c2-087ae46d118e
-- title:
--   Every small central sum has controlled padded models
-- statement:
--   The restricted tails defining x and y construct a word with fixed core 1,4,1. Its central height is 4+x+y, and B uniformly bounds all other positions in every padded truncation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-family and m2a:completed-bounds.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_model (x y : ℝ) (hx : x ∈ upperKOne) (hy : y ∈ upperKOne) :
    upperModel (4 + x + y) := by
  sorry

end Freiman
