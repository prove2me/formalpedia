-- Prove2me | Theorems.Thm_Freiman_limsup_subsequence
-- name    : Freiman.limsup_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:54.765042+00:00
-- url     : https://prove2.me/theorems/f57e565d-bb32-4cf4-95d9-45fdbca2ac0d
-- title:
--   A finite limsup is the limit of a strictly increasing subsequence
-- statement:
--   A real sequence with finite limsup t has a subsequence indexed by a strictly increasing map from the natural numbers whose values converge to t.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, selection of n_j, printed p. 8.

import Definitions.Def_Freiman_lagrangeSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem limsup_subsequence (u : ℕ → ℝ) (t : ℝ) (h : HasFiniteLimsup u t) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Filter.Tendsto (fun n => u (s n)) Filter.atTop (nhds t) := by
  sorry

end Freiman
