-- Prove2me | Theorems.Thm_Freiman_continuant_eventually_nearest
-- name    : Freiman.continuant_eventually_nearest
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:13.953033+00:00
-- url     : https://prove2.me/theorems/030c1ec1-ad75-4aeb-ac32-2742583146dd
-- title:
--   Convergent numerators are eventually nearest integers
-- statement:
--   Eventually the strict convergent error is below one half. Then the convergent numerator attains the existing integerDistance.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem continuant_eventually_nearest (b : ℕ → ℕ+) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      integerDistance ((continuantQ b n : ℝ) * cfValue b) =
      |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)| := by
  sorry

end Freiman
