-- Prove2me | Theorems.Thm_Freiman_continuant_convergent_eq
-- name    : Freiman.continuant_convergent_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:52.352346+00:00
-- url     : https://prove2.me/theorems/c0f2507f-d660-4c9d-b324-9350e7503beb
-- title:
--   Existing convergents equal continuant ratios
-- statement:
--   The existing recursively evaluated cfConvergent, with exactly n digits, equals p_n/q_n. This supplies the required link to the platform definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_convergent_eq (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b n = (continuantP b n : ℝ) / continuantQ b n := by
  sorry

end Freiman
