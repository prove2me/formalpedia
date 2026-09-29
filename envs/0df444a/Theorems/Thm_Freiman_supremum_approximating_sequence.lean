-- Prove2me | Theorems.Thm_Freiman_supremum_approximating_sequence
-- name    : Freiman.supremum_approximating_sequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:42.581625+00:00
-- url     : https://prove2.me/theorems/d0a6e814-37f5-4b63-9e58-b6bd639b7483
-- title:
--   A finite supremum of integer-indexed values admits an approximating sequence
-- statement:
--   If t is an upper bound for an integer-indexed real family and values approach t from below arbitrarily closely, there exists a sequence of integer indices along which the family converges to t. The indices need not be monotone or distinct.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §20.1, Lemma 20.1, choice of centres in its proof, printed p. 65.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem supremum_approximating_sequence (f : ℤ → ℝ) (t : ℝ)
    (hmax : ∀ i : ℤ, f i ≤ t)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ i : ℤ, t - ε < f i) :
    ∃ s : ℕ → ℤ, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds t) := by
  sorry

end Freiman
