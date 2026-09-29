-- Prove2me | Theorems.Thm_Freiman_cfValue_prefix
-- name    : Freiman.cfValue_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:44.92805+00:00
-- url     : https://prove2.me/theorems/e73997c8-021c-4bdc-a21b-cd9562b78406
-- title:
--   Existing cfValue equals finite prefix applied to its actual tail
-- statement:
--   For every positive digit sequence and prefix length m, its existing supremum-of-even-convergents value equals evaluation of the first m digits at the cfValue of the shifted sequence. This is an explicit bridge to the existing definition, not a replacement definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_prefixEval

namespace Freiman

theorem cfValue_prefix (b : ℕ → ℕ+) (m : ℕ) :
    cfValue b = prefixEval ((List.range m).map b)
      (cfValue (fun k => b (m + k))) := by
  sorry

end Freiman
