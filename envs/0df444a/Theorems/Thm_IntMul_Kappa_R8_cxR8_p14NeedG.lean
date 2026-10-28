-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_cxR8_p14NeedG
-- name    : IntMul.Kappa.R8.cxR8_p14NeedG
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:05:17.23662+00:00
-- url     : https://prove2.me/theorems/e57897ba-00e0-447c-a10f-54aafc7745d5
-- title:
--   Prop.~14 need for Jain.cxR8 on every Ok parameter
-- statement:
--   For every ok round-six parameter $P$, the Prop.~14 need package `P14NeedG` holds at width budget $W_c=12869228$, machine width $m_c=576$, and histogram `Jain.cxR8`.
--
--   This packages the numeric side conditions of `p14NeedG_all` (width bounds, the exponential comparison with a threshold $p_0$, and $p_0\le 2+m_c\log s_c$) specialised to the round-eight complex certificate.
-- source:
--   xuanji R8 framework sketch Layer D; wraps R6.IL3H.p14NeedG_all at Jain.cxR8

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.R6 IntMul.Kappa.Jain

/-- The parametric Prop.~14 interface at the round-eight complex histogram holds for every ok parameter. -/
theorem cxR8_p14NeedG (P : Prm) (hP : P.Ok) : P14NeedG 12869228 576 cxR8 P := by
  sorry

end IntMul.Kappa.R8
