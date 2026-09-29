-- Prove2me | Theorems.Thm_Freiman_continuant_denominator_escape
-- name    : Freiman.continuant_denominator_escape
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:54.87998+00:00
-- url     : https://prove2.me/theorems/8c399ef3-ea88-4a91-9ed6-45cb9914e8af
-- title:
--   Convergent denominators escape every bound
-- statement:
--   The Fibonacci lower bound makes the denominators tend to infinity. The conclusion is stated with explicit quantifiers needed by the epsilon arguments.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, after found:continuity

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_denominator_escape (b : ℕ → ℕ+) :
    ∀ R : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R ≤ continuantQ b n := by
  sorry

end Freiman
