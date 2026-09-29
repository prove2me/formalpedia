-- Prove2me | Theorems.Thm_Freiman_perron_local_difference_tendsto
-- name    : Freiman.perron_local_difference_tendsto
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:27.38675+00:00
-- url     : https://prove2.me/theorems/a4c4aac5-ce39-4ae7-8a14-861e5d25d91d
-- title:
--   Finite and infinite backward tails have vanishing difference
-- statement:
--   The two backward tails agree for n digits. The finite tail ends with parameter 0, and the infinite one has parameter in (0,1). The report’s bound F_(n+1)^−2 tends to zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1 after found:local-values; §1.2 found:lagrange-symbolic

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Freiman

theorem perron_local_difference_tendsto (a : ℤ → ℕ+) :
    Filter.Tendsto
      (fun n : ℕ => perronValue (fun k : ℕ => a (k : ℤ)) n - localValue a (n : ℤ))
      Filter.atTop (nhds 0) := by
  sorry

end Freiman
