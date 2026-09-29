-- Prove2me | Theorems.Thm_Freiman_hasFiniteLimsup_congr_of_tendsto_sub_zero
-- name    : Freiman.hasFiniteLimsup_congr_of_tendsto_sub_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:22.68624+00:00
-- url     : https://prove2.me/theorems/f41b6036-aacc-4ecc-8e08-d2231e9c1525
-- title:
--   The epsilon limsup is unchanged by a vanishing difference
-- statement:
--   The two explicit epsilon clauses are preserved when the difference of the two real sequences tends to zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:lagrange-symbolic

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Freiman

theorem hasFiniteLimsup_congr_of_tendsto_sub_zero (u v : ℕ → ℝ) (t : ℝ) (h : Filter.Tendsto (fun n => u n - v n) Filter.atTop (nhds 0)) :
    HasFiniteLimsup u t ↔ HasFiniteLimsup v t := by
  sorry

end Freiman
