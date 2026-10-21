-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR7plain_rankSum
-- name    : IntMul.Kappa.R8.bitR7plain_rankSum
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:29:19.156221+00:00
-- url     : https://prove2.me/theorems/f92ccd7d-0708-4758-9f17-43c2c2dd0a60
-- title:
--   Rank sum of Jain.bitR7plain equals $55\,395\,128\,481$
-- statement:
--   **Rank sum of the round-seven plain bit histogram.**
--
--   Let $h^{\mathrm{old}}=\mathrm{Jain.bitR7plain}$ be the child-width histogram of Jain's round-seven bit interchange on witness 2 with the round-six entrance corner (width $m=529$, role count $W=104\,719\,230$). Its weighted rank sum equals
--   $$\mathrm{histRankSum}(h^{\mathrm{old}})=\sum_w w\,n_w=55\,395\,128\,481.$$
--
--   This matches the kernel certificate `bitplain_rank_sum` in `lean/Round7.lean` and the frozen JSON field `bitplain.s` in `lean/round7-histograms.json`. It is the bit-side rank sum paired with the stopped-mix parameter $a_{\mathrm{old}}$ of round eight.
--
--   **Formalization Note.** `histRankSum` is from `IntMul_KappaFramework`; `bitR7plain` is from `IntMul_KappaJainData`.
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — lean/Round7.lean theorem bitplain_rank_sum; lean/round7-histograms.json key bitplain.s = 55395128481

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.Jain

/-- Rank sum of the round-seven plain bit histogram (witness 2, round-six entrance corner). -/
theorem bitR7plain_rankSum : histRankSum bitR7plain = 55395128481 := by
  sorry

end IntMul.Kappa.R8
