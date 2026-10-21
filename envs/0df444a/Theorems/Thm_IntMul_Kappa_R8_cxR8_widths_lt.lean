-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_cxR8_widths_lt
-- name    : IntMul.Kappa.R8.cxR8_widths_lt
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:18:22.237018+00:00
-- url     : https://prove2.me/theorems/41e67164-53ef-4ae2-a96e-21405095b182
-- title:
--   Round-eight complex histogram child widths are less than 576
-- statement:
--   Let `cxR8` be S. Jain's round-eight complex-side child-width histogram. The complex interchange runs at width $m=576$. The interface `Prop8IfaceH` requires every recorded child width to satisfy $w<m$. This theorem is the finite check
--
--   $$
--   \forall (w,n_w)\in\texttt{cxR8},\qquad w<576.
--   $$
--
--   (The largest listed child is $529$.)
-- source:
--   S. Jain, integer-mult-kappa, lean/Round8.lean cxHist; Def_IntMul_KappaJainData Jain.cxR8; Prop8IfaceH.small in Def_IntMul_Kappa_R6_Defs2

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa.Jain

/-- Every child width appearing in `Jain.cxR8` is strictly less than the complex-network width $m = 576$
(as required by `Prop8IfaceH.small`). -/
theorem cxR8_widths_lt : ∀ p ∈ cxR8, p.1 < 576 := by
  sorry

end IntMul.Kappa.R8
