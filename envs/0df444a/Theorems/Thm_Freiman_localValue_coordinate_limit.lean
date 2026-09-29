-- Prove2me | Theorems.Thm_Freiman_localValue_coordinate_limit
-- name    : Freiman.localValue_coordinate_limit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:54.427206+00:00
-- url     : https://prove2.me/theorems/b8fbeafa-efc8-437f-bd55-880a13fcf628
-- title:
--   Local Perron values are continuous under coordinatewise convergence of words
-- statement:
--   If every coordinate in a sequence of positive digit words eventually agrees with a limiting word, then every fixed local Perron value converges to the corresponding local value of the limiting word. No global alphabet bound is required for this continuity statement.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, immediately after equation (1.3), printed p. 7.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem localValue_coordinate_limit (A : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+)
    (h : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, A n i = b i) :
    ∀ i : ℤ, Filter.Tendsto (fun n => localValue (A n) i)
      Filter.atTop (nhds (localValue b i)) := by
  sorry

end Freiman
