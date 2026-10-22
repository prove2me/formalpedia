-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_bitNetR8_mom
-- name    : IntMul.Kappa.R8.bitNetR8_mom
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:06:55.65409+00:00
-- url     : https://prove2.me/theorems/2e2fbbed-4b7d-41fb-805a-f7ccbd667355
-- title:
--   Round-eight bit network dominates Jain.bitR8 moments
-- statement:
--   **Round-eight bit network, moment-dominance form.**
--
--   There exists a QH-network $C$ over $\mathbb{Z}/2\mathbb{Z}$ with $W_b = 104\,719\,230$ roles and width $m_b = 529$, together with a prime cutoff $q_0$, such that:
--
--   1. $C$ runs correctly (`RunsOK`);
--   2. for every prime $q > q_0$ and every exponent $f$, the edge and formal checks hold at the prime power $q^f$;
--   3. for every exponent $\tau \in (0,1]$, the child-width moment of $C$ is at most that of Jain's round-eight bit histogram:
--      $$\mathrm{histMoment}(C.\mathrm{hist},\,529,\,\tau)\le \mathrm{histMoment}(h^{\mathrm{bit}},\,529,\,\tau),$$
--      where $h^{\mathrm{bit}}=\mathrm{Jain.bitR8}$ is the opposite-bank-order bit interchange of round eight (width classes up to $22$, a $484$-class, and the $506$–$528$ tail).
--
--   In the platform vocabulary this is exactly
--   $$\mathrm{Bit.BitNetMomStmtG}\,104719230\,529\,\mathrm{Jain.bitR8}.$$
--   At the round-six constants $(148225616,529,\mathrm{Jain.bitR6})$ the same predicate is `Bit.BitNetR6MomStmt`, already proved as `IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp`.
--
--   This is the bit-network machine interface needed to feed Jain's round-eight histogram into the parametric assembly `IntMul.Kappa.R6.kappa_finalG_at`, and thence into `IntMul.Kappa.jain_round8_framework`.
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README 'Round eight' (bit side: opposite bank orders on round-seven witness 2; W=104719230, m=529), lean/Round8.lean (bitHist), independent/round8-oppbank/; machine interface shape from Prove2me IntMul.Kappa.R6.Bit.BitNetMomStmtG (Def_IntMul_Kappa_RG_Defs) and the proved round-six instance IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp; conditional on OpenAI Integer multiplication below n log n (23 Sep 2026) and Colkitt integer-mult-bounds

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Round-eight bit interchange (opposite bank orders on the round-seven witness 2): a QH-network
over `ZMod 2` with $W = 104719230$ roles and width $m = 529$ whose child-width moments are
dominated by `Jain.bitR8`. -/
theorem bitNetR8_mom : BitNetMomStmtG 104719230 529 Jain.bitR8 := by
  sorry

end IntMul.Kappa.R8
