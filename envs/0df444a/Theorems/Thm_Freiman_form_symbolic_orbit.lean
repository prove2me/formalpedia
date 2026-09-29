-- Prove2me | Theorems.Thm_Freiman_form_symbolic_orbit
-- name    : Freiman.form_symbolic_orbit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:16.795298+00:00
-- url     : https://prove2.me/theorems/c6469673-f17b-47ab-8193-0cf6ddd54c50
-- title:
--   Every two-sided digit string yields its reduced irrational orbit
-- statement:
--   Define alpha and beta by the right and left infinite tails of a. The accepted cf_convergence theorem gives irrationality and unit-interval bounds; stripping a digit gives both recurrences and identifies the floors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, converse direction of found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_symbolic_orbit (a : ℤ → ℕ+) :
    ∃ R : ReducedOrbit, R.digits = a := by
  sorry

end Freiman
