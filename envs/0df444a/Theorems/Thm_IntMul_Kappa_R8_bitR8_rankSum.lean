-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR8_rankSum
-- name    : IntMul.Kappa.R8.bitR8_rankSum
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:29:19.843988+00:00
-- url     : https://prove2.me/theorems/9c36850b-71e0-4bbb-83dc-3201a11ea193
-- title:
--   Rank sum of Jain.bitR8 equals $55\,395\,128\,481$
-- statement:
--   **Rank sum of the round-eight bit histogram.**
--
--   Let $h^{\mathrm{bit}}=\mathrm{Jain.bitR8}$ be the child-width histogram of Jain's round-eight bit interchange (opposite bank orders on round-seven witness 2). Its weighted rank sum equals
--   $$\mathrm{histRankSum}(h^{\mathrm{bit}})=\sum_w w\,n_w=55\,395\,128\,481,$$
--   the same value as for `Jain.bitR7plain`. This matches `bit_rank_sum` in `lean/Round8.lean` / the bit-phase rank certificate of `round8_certificates`, and is consistent with the opp-bank recompile preserving total child width while reshaping the histogram bins.
--
--   **Formalization Note.** `histRankSum` is from `IntMul_KappaFramework`; `bitR8` is from `IntMul_KappaJainData`.
-- source:
--   S. Jain, integer-mult-kappa, lean/Round8.lean theorem bit_rank_sum; Prove2me IntMul.Kappa.round8_certificates (bit-phase rank sum); lean/round7-histograms.json bitplain.s and round8 bit hist share s=55395128481

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.Jain

/-- Rank sum of the round-eight bit histogram (opposite bank orders); equals the plain rank sum. -/
theorem bitR8_rankSum : histRankSum bitR8 = 55395128481 := by
  sorry

end IntMul.Kappa.R8
