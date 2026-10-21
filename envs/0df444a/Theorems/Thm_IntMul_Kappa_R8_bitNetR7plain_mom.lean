-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitNetR7plain_mom
-- name    : IntMul.Kappa.R8.bitNetR7plain_mom
-- status  : Open
-- author  : @Ethan
-- created : 2026-10-21T05:14:06.540738+00:00
-- url     : https://prove2.me/theorems/fefc194e-5f71-4f82-bf41-128e02ff35ff
-- title:
--   Round-seven plain bit network dominates Jain.bitR7plain moments
-- statement:
--   **Round-seven plain bit network (witness 2), moment-dominance form.**
--
--   There exists a QH-network $C$ over $\mathbb{Z}/2\mathbb{Z}$ with $W_b = 104\,719\,230$ roles and width $m_b = 529$, together with a prime cutoff $q_0$, such that:
--
--   1. $C$ runs correctly (`RunsOK`);
--   2. for every prime $q > q_0$ and every exponent $f$, the edge and formal checks hold at the prime power $q^f$;
--   3. for every exponent $\tau \in (0,1]$, the child-width moment of $C$ is at most that of Jain's round-seven *plain* bit histogram (witness 2 with the round-six entrance corner):
--      $$\mathrm{histMoment}(C.\mathrm{hist},\,529,\,\tau)\le \mathrm{histMoment}(h^{\mathrm{old}},\,529,\,\tau),$$
--      where $h^{\mathrm{old}}=\mathrm{Jain.bitR7plain}$ is the histogram whose certified saving is the $a_{\mathrm{old}}$ of round eight's stopped bit interchange.
--
--   In the platform vocabulary this is exactly
--   $$\mathrm{Bit.BitNetMomStmtG}\,104719230\,529\,\mathrm{Jain.bitR7plain}.$$
--
--   **Relation to neighbouring nodes.** The sister statement `IntMul.Kappa.R6.Bit.bitNetR7_mom` asserts the same interface for the *other* round-seven witness (`Jain.bitR7`, $W=108\,516\,254$). The round-eight opposite-bank network is `IntMul.Kappa.R8.bitNetR8_mom` (same $W=104\,719\,230$, histogram `Jain.bitR8`). The proved round-six instance is `IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp`.
--
--   **Role in round eight.** Together with moment monotonicity in the exponent, this leaf discharges the stopped-mix branch $a_b\le a_{\mathrm{old}}$ of `jain_round8_framework`, feeding `kappa_finalG_at` when the convex combination sits on the plain side.
--
--   **Formalization Note.** `BitNetMomStmtG` is from `IntMul_Kappa_RG_Defs`; the histogram is from `IntMul_KappaJainData` (`lean/Round7.lean`, `bitplainHist`).
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README 'Round seven' / 'Round eight' (a_old = round-seven saving of witness 2 with round-six entrance corner; W=104719230, m=529), lean/Round7.lean (bitplainHist), certificates/round7/, independent/deferred-readout/; machine interface shape from Prove2me IntMul.Kappa.R6.Bit.BitNetMomStmtG (Def_IntMul_Kappa_RG_Defs); sister Open node IntMul.Kappa.R6.Bit.bitNetR7_mom (Jain.bitR7, W=108516254); proved template IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp; conditional on OpenAI Integer multiplication below n log n (23 Sep 2026) and Colkitt integer-mult-bounds

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Round-seven bit network, witness 2 with the round-six entrance corner (`bitplainHist`):
a QH-network over `ZMod 2` with $W = 104719230$ roles and width $m = 529$ whose
child-width moments are dominated by `Jain.bitR7plain`. This is the `a_old` network
of round eight's stopped bit interchange. -/
theorem bitNetR7plain_mom : BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  sorry

end IntMul.Kappa.R8
