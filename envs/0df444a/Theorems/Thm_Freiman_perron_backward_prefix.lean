-- Prove2me | Theorems.Thm_Freiman_perron_backward_prefix
-- name    : Freiman.perron_backward_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:46.325522+00:00
-- url     : https://prove2.me/theorems/02669bc9-be58-40b4-b46e-39d71e2d15c3
-- title:
--   Reverse finite list matches the backward convergent
-- statement:
--   The finite fraction of the reversed first n digits is exactly the nth convergent of the infinite backward word viewed from position n. This states the index and reversal convention needed by the existing perronValue definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_cfValue

namespace Freiman

theorem perron_backward_prefix (a : ℤ → ℕ+) (n : ℕ) :
    finiteCF (((List.range n).map (fun k : ℕ => a (k : ℤ))).reverse) =
      cfConvergent (fun k : ℕ => a ((n : ℤ) - (k : ℤ) - 1)) n := by
  sorry

end Freiman
