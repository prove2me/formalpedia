-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_bitR7plain_bitR8_rankSum_eq
-- name    : IntMul.Kappa.R8.Bit.bitR7plain_bitR8_rankSum_eq
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:30:38.413586+00:00
-- url     : https://prove2.me/theorems/efa55ec9-7a84-4186-9b4c-1f5e0f87fafd
-- title:
--   Round-seven plain and round-eight bit histograms share the same rank sum
-- statement:
--   Let `bitR7plain` and `bitR8` be S. Jain's frozen child-width histograms for the round-seven plain witness 2 and its round-eight opposite-bank recompile. The rank sum
--   $$s=\sum_{(w,n_w)} w\,n_w=\mathrm{histRankSum}$$
--   is the same for both lists (as asserted by `independent/round8-oppbank/bit_hist.py`: $W$ and $s$ equal round seven's). This theorem is the corresponding finite identity on Prove2me.
-- source:
--   S. Jain integer-mult-kappa independent/round8-oppbank/bit_hist.py (assert W,s equal); Def_IntMul_KappaJainData

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit

open IntMul.Kappa IntMul.Kappa.Jain

/-- Jain's opposite-bank recompile preserves the rank sum $s=\sum w\,n_w$ (and $W$): 
`histRankSum bitR7plain = histRankSum bitR8`. -/
theorem bitR7plain_bitR8_rankSum_eq :
    histRankSum bitR7plain = histRankSum bitR8 := by
  sorry

end IntMul.Kappa.R8.Bit
