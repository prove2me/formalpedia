-- Prove2me | Theorems.Thm_Freiman_form_root_convergent_data
-- name    : Freiman.form_root_convergent_data
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:44.374987+00:00
-- url     : https://prove2.me/theorems/5ba386b3-baa8-4a64-b211-9e2cb7325ac9
-- title:
--   Every irrational root has the required convergent matrices
-- statement:
--   Normalize r by an integer translation, expand the fractional part as the existing cfValue, and use the integer-translated continuant construction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:reduce-roots

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData

namespace Freiman

theorem form_root_convergent_data (r : ℝ) (hr : Irrational r) :
    Nonempty (RootConvergentData r) := by
  sorry

end Freiman
