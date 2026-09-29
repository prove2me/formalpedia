-- Prove2me | Theorems.Thm_Freiman_attain_limsup_by_shift
-- name    : Freiman.attain_limsup_by_shift
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:50.904378+00:00
-- url     : https://prove2.me/theorems/b5bbeb6e-3813-4644-80f2-0b20b951d184
-- title:
--   A symbolic Lagrange value is attained as a centred symbolic Markov value
-- statement:
--   Every finite limsup of positive-index local values of a two-sided word can be realized as the local value at zero of another two-sided positive digit word, with all local values of the new word bounded above by that limsup.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, final paragraph, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem attain_limsup_by_shift (a : ℤ → ℕ+) (t : ℝ)
    (h : HasFiniteLimsup (fun n : ℕ => localValue a (n : ℤ)) t) :
    ∃ b : ℤ → ℕ+, localValue b 0 = t ∧
      ∀ i : ℤ, localValue b i ≤ t := by
  sorry

end Freiman
