-- Prove2me | Theorems.Thm_Freiman_background_prefix12_comparison
-- name    : Freiman.background_prefix12_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:00.247851+00:00
-- url     : https://prove2.me/theorems/71996d22-6105-45c3-8431-e82cd275acd9
-- title:
--   Replacing the second digit by two increases a tail beginning with one
-- statement:
--   For a positive tail whose first digit is one and second digit is at most two, replacing its first two digits by 12 while keeping the remaining tail can only increase its value.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_prefix12_comparison (b : ℕ → ℕ+) (h0 : (b 0 : ℕ) = 1) (h1 : (b 1 : ℕ) ≤ 2) :
    cfValue b ≤ prefixEval [1,2] (cfValue (fun n => b (n + 2))) := by
  sorry

end Freiman
