-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitR8_widths
-- name    : IntMul.Kappa.R8.bitR8_widths
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:29:17.300149+00:00
-- url     : https://prove2.me/theorems/50cdff05-90ad-4eeb-be50-a48e6266555d
-- title:
--   Every width in Jain.bitR8 lies in $(0,529]$
-- statement:
--   **Width bounds for the round-eight bit histogram.**
--
--   Every child-width pair $(w,n)$ in Jain's round-eight bit histogram $h^{\mathrm{bit}}=\mathrm{Jain.bitR8}$ (opposite bank orders on the round-seven witness 2; width bound $m=529$) satisfies
--   $$0 < w \le 529.$$
--
--   Together with the proved `histMoment_mono_tau`, this unlocks upgrading a moment bound at exponent $1-a^*$ to the stopped-mix exponent $1-a_b$ whenever $a_b\le a^*$. The sister lemma `bitR8_widths_le` only records $w\le 529$; the strict positivity $w>0$ is required by the monotonicity hypothesis.
--
--   **Formalization Note.** `bitR8` is from `IntMul_KappaJainData` (`lean/Round8.lean`, `bitHist`).
-- source:
--   S. Jain, integer-mult-kappa, lean/Round8.lean (bitHist), https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f; used with Prove2me IntMul.Kappa.R8.histMoment_mono_tau and IntMul.Kappa.R8.bitR8_widths_le

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa.Jain

/-- Width side-condition for applying `histMoment_mono_tau` to the round-eight bit histogram.
Stronger than `bitR8_widths_le` by also requiring positive widths. -/
theorem bitR8_widths : ∀ p ∈ bitR8, 0 < p.1 ∧ p.1 ≤ 529 := by
  sorry

end IntMul.Kappa.R8
