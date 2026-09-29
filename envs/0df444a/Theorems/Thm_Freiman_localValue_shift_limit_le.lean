-- Prove2me | Theorems.Thm_Freiman_localValue_shift_limit_le
-- name    : Freiman.localValue_shift_limit_le
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:39.345342+00:00
-- url     : https://prove2.me/theorems/e3ad4dac-3b80-4f73-93d3-dd168a99effc
-- title:
--   A finite limit along shifted increasing centres is at most the right limsup
-- statement:
--   Let the positive-index local values of a word have finite limsup t. If, at a fixed integer offset from strictly increasing nonnegative centres, the local values converge to r, then r is at most t.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, inequality for every fixed r in the limiting word, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem localValue_shift_limit_le (a : ℤ → ℕ+) (t : ℝ)
    (h : HasFiniteLimsup (fun n : ℕ => localValue a (n : ℤ)) t)
    (s : ℕ → ℕ) (hs : StrictMono s) (i : ℤ) (r : ℝ)
    (hr : Filter.Tendsto (fun n => localValue a ((s n : ℤ) + i))
      Filter.atTop (nhds r)) :
    r ≤ t := by
  sorry

end Freiman
