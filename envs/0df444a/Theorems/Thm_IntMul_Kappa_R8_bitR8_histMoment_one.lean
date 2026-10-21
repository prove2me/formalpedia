-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR8_histMoment_one
-- name    : IntMul.Kappa.R8.bitR8_histMoment_one
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:38:43.895888+00:00
-- url     : https://prove2.me/theorems/ac9a5cef-9d78-4536-b8e9-2f733b8c6224
-- title:
--   Round-eight bit histogram moment at exponent 1
-- statement:
--   For Jain's round-eight bit histogram `bitR8` at width $m=529$,
--   $$\mathrm{histMoment}(\texttt{bitR8},529,1)=\frac{55395128481}{529},$$
--   where $55395128481=\mathrm{histRankSum}(\texttt{bitR8})$ is the proved rank-sum identity. The same value holds for `bitR7plain` (equal rank sums under opposite-bank recompile).
-- source:
--   IntMul.Kappa.histMoment_one; IntMul.Kappa.R8.bitR8_rankSum; Def_IntMul_KappaJainData

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.Jain

/-- Specialising `histMoment_one` at `Jain.bitR8` and $m=529$, using the proved rank sum
$55395128481$. -/
theorem bitR8_histMoment_one :
    histMoment bitR8 529 1 = (55395128481 : ℝ) / 529 := by
  sorry

end IntMul.Kappa.R8
