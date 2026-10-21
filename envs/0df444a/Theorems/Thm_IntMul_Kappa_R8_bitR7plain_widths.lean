-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR7plain_widths
-- name    : IntMul.Kappa.R8.bitR7plain_widths
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:15:53.614861+00:00
-- url     : https://prove2.me/theorems/0c94f7d5-57db-448c-9e8f-9aeb12d11ef6
-- title:
--   Every width in Jain.bitR7plain lies in $(0,529]$
-- statement:
--   **Width bounds for the round-seven plain bit histogram.**
--
--   Every child-width pair $(w,n)$ in Jain's round-seven plain bit histogram $h^{\mathrm{old}}=\mathrm{Jain.bitR7plain}$ (witness 2 with the round-six entrance corner; width bound $m=529$) satisfies
--   $$0 < w \le 529.$$
--
--   This is the side-condition needed to apply the proved monotonicity lemma `IntMul.Kappa.R8.histMoment_mono_tau` when upgrading a moment bound at exponent $1-a_{\mathrm{old}}$ to the stopped-mix exponent $1-a_b$ in the $a_b\le a_{\mathrm{old}}$ branch of `jain_round8_framework`.
--
--   **Formalization Note.** The list `bitR7plain` is from `IntMul_KappaJainData`, transcribed from `lean/Round7.lean` (`bitplainHist`).
-- source:
--   S. Jain, integer-mult-kappa, lean/Round7.lean (bitplainHist), https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f; used with Prove2me IntMul.Kappa.R8.histMoment_mono_tau and IntMul.Kappa.jain_round8_framework

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa.Jain

/-- Width side-condition for applying `histMoment_mono_tau` to the round-seven plain histogram. -/
theorem bitR7plain_widths : ∀ p ∈ bitR7plain, 0 < p.1 ∧ p.1 ≤ 529 := by
  sorry

end IntMul.Kappa.R8
