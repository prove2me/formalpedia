-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR8_widths_le
-- name    : IntMul.Kappa.R8.bitR8_widths_le
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:18:24.067988+00:00
-- url     : https://prove2.me/theorems/717ea891-59c7-4abf-88e0-86ece3798498
-- title:
--   Round-eight bit histogram child widths are at most 529
-- statement:
--   Let `bitR8` be S. Jain's round-eight bit-side child-width histogram (pairs $(w,n_w)$ from `lean/Round8.lean`). The underlying QH-network has width $m=529$. This theorem asserts the finite inspection
--
--   $$
--   \forall (w,n_w)\in\texttt{bitR8},\qquad w\le 529.
--   $$
--
--   It is the bit-side width guard used by moment comparisons and by any QH-network whose child widths are required to be at most $m$.
-- source:
--   S. Jain, integer-mult-kappa, lean/Round8.lean bitHist; Def_IntMul_KappaJainData Jain.bitR8

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa.Jain

/-- Every child width appearing in `Jain.bitR8` is at most the bit-network width $m = 529$. -/
theorem bitR8_widths_le : ∀ p ∈ bitR8, p.1 ≤ 529 := by
  sorry

end IntMul.Kappa.R8
