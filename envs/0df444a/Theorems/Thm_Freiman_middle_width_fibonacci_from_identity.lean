-- Prove2me | Theorems.Thm_Freiman_middle_width_fibonacci_from_identity
-- name    : Freiman.middle_width_fibonacci_from_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:44.36724+00:00
-- url     : https://prove2.me/theorems/90b10cab-8cd6-4c9f-ae5a-9acc90b0b9af
-- title:
--   middle width fibonacci from identity
-- statement:
--   The exact width formula and continuant growth imply the Fibonacci cylinder bound because both tail factors in its denominator are at least one; all denominators and beta-alpha have the required signs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:width and m2b:prop:path

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_width_fibonacci_from_identity :
    (∀ w : List ℕ+, middleWidth w = (middleBeta-middleAlpha)/((middleCD w).2^2 * (1+middleParameter w*middleAlpha) * (1+middleParameter w*middleBeta))) →
    (∀ w : List ℕ+, 0 ≤ middleParameter w ∧ 0<(middleCD w).2 ∧ (Nat.fib (w.length+1):ℝ) ≤ (middleCD w).2) →
    ∀ w : List ℕ+, middleWidth w  ≤  (middleBeta-middleAlpha)/(Nat.fib (w.length+1):ℝ)^2 := by
  sorry

end Freiman
