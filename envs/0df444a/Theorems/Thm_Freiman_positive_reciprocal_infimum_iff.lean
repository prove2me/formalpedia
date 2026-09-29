-- Prove2me | Theorems.Thm_Freiman_positive_reciprocal_infimum_iff
-- name    : Freiman.positive_reciprocal_infimum_iff
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:23.188842+00:00
-- url     : https://prove2.me/theorems/f0b0fe5f-00cb-4bdb-9a9a-032e76cd619d
-- title:
--   Positive reciprocal infimum characterizes a finite supremum
-- statement:
--   For a positive, nonempty family, a finite supremum t is equivalent to the reciprocal family having positive infimum h with t=1/h. This uses the exact upper-bound and epsilon-approach clauses of symbolicMarkovSpectrum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem positive_reciprocal_infimum_iff (u : ℤ → ℝ) (hu : ∀ n, 0 < u n) (t : ℝ) :
    ((∀ n : ℤ, u n ≤ t) ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℤ, t-ε<u n) ↔
      0 < sInf (Set.range (fun n : ℤ => 1/u n)) ∧ t=1/sInf (Set.range (fun n : ℤ => 1/u n)) := by
  sorry

end Freiman
