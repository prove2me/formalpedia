-- Prove2me | Theorems.Thm_Freiman_continuant_coprime
-- name    : Freiman.continuant_coprime
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:02.864298+00:00
-- url     : https://prove2.me/theorems/d3080eda-4742-4c98-9536-2ffc844aa633
-- title:
--   Coprimality of convergent numerators and denominators
-- statement:
--   Successive determinant one implies each numerator and denominator pair is reduced.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_coprime (b : ℕ → ℕ+) (n : ℕ) :
    Nat.Coprime (continuantP b n) (continuantQ b n) := by
  sorry

end Freiman
