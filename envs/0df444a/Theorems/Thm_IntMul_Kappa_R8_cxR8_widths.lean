-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_cxR8_widths
-- name    : IntMul.Kappa.R8.cxR8_widths
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:04:47.812271+00:00
-- url     : https://prove2.me/theorems/4aa2b8d5-88e1-4355-9559-4ee5fc2695f3
-- title:
--   Positive bounded widths of Jain.cxR8
-- statement:
--   Every child width appearing in the round-eight complex histogram `Jain.cxR8` is strictly positive and at most $529$.
--
--   That is, for every pair $(w,n_w)$ in the histogram,
--   $$
--   0 < w \le 529.
--   $$
--   This is the width hypothesis needed to instantiate the parametric Prop.~14 interface at $w_{\max}=529$ and $m_c=576$, and to compare complex moments across exponents.
-- source:
--   xuanji / Jain integer-mult-kappa round 8 complex histogram (Def_IntMul_KappaJainData.cxR8); side condition for R6.IL3H.p14NeedG_all at Wc=12869228, mc=576

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa.Jain

/-- Width side-condition for `p14NeedG_all` / moment comparisons on `Jain.cxR8`:
every child width lies in $(0, 529]$. -/
theorem cxR8_widths : ∀ p ∈ cxR8, 0 < p.1 ∧ p.1 ≤ 529 := by
  sorry

end IntMul.Kappa.R8
