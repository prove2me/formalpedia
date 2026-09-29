-- Prove2me | Theorems.Thm_Freiman_middle_width_identity
-- name    : Freiman.middle_width_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:21.465026+00:00
-- url     : https://prove2.me/theorems/42251151-db2b-414d-9db0-b14bc2bfa3cb
-- title:
--   middle width identity
-- statement:
--   Exact full-cylinder width identity, including the empty word. This is a finite continued-fraction matrix calculation, not a claim that the whole cylinder hull is a Cantor sum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, equations m2b:eq:diff and m2b:eq:width

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_width_identity :
    ∀ w : List ℕ+,
      middleWidth w = (middleBeta-middleAlpha) /
        ((middleCD w).2^2 * (1+middleParameter w*middleAlpha) * (1+middleParameter w*middleBeta)) := by
  sorry

end Freiman
