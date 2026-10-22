-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_oppbank_mom_of_plain
-- name    : IntMul.Kappa.R8.Bit.oppbank_mom_of_plain
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:17:11.802099+00:00
-- url     : https://prove2.me/theorems/b40cfe62-1258-4b45-aede-41e7ad60d5fe
-- title:
--   Opposite-bank recompile lifts bitR7plain moment network to bitR8
-- statement:
--   Round eight's bit-side witness (S. Jain, *integer-mult-kappa*, round eight) reuses the deferred round-seven witness 2: the same schedule, frames and payload word that produce the child-width histogram `bitplainHist` ($W = 104719230$ roles, width $m = 529$), whose certified saving is the stopped-interchange parameter $a_{\mathrm{old}}$.
--
--   The only change is the address geometry of each interchange. In a generic rational basis every residual idempotent of rank $r$ has nonzero leading principal minors $1,\ldots,r$; storing the tail bank in reverse atom order collapses the generic anti-diagonal Bruhat cell of each partial swap to one contiguous reversed run, so a residual of rank $r$ becomes a single child of width $r$. An outer wrapper of three lower updates restores the ordinary interchange. The resulting child-width multiset is `bitHist` / `Jain.bitR8`.
--
--   On Prove2me the bit-network obligation is the parametric moment statement `BitNetMomStmtG Wb mb hb`: existence of a QH-network over $\mathbb{Z}/2\mathbb{Z}$ with $W_b$ roles and width $m_b$ that runs correctly, is edge- and formally OK at all large prime powers, and whose child-width moments are dominated by those of the histogram $h_b$ at every exponent $\tau\in(0,1]$.
--
--   This problem asks for the opposite-bank recompile as a map of those statements: any witness of
--
--   $$
--   \texttt{BitNetMomStmtG }104719230\ 529\ \texttt{Jain.bitR7plain}
--   $$
--
--   yields a witness of
--
--   $$
--   \texttt{BitNetMomStmtG }104719230\ 529\ \texttt{Jain.bitR8}.
--   $$
--
--   Together with the open leaf `IntMul.Kappa.R8.bitNetR7plain_mom`, this reduces `IntMul.Kappa.R8.bitNetR8_mom`.
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README 'Round eight' bit side (opposite bank orders / icekylinx on round-seven witness 2); independent/round8-oppbank/; lean/Round8.lean bitHist vs lean/Round7.lean bitplainHist; Prove2me BitNetMomStmtG in Def_IntMul_Kappa_RG_Defs; parents IntMul.Kappa.R8.bitNetR8_mom and IntMul.Kappa.R8.bitNetR7plain_mom

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Jain's round-eight bit interchange keeps the round-seven witness-2 schedule, frames and
payload word (`bitplainHist` / `Jain.bitR7plain`, $W = 104719230$, $m = 529$) and only
recompiles the address geometry: opposite bank orders (icekylinx) turn each residual of
rank $r$ into one contiguous reversed child of width $r$, producing histogram `Jain.bitR8`.

This lemma packages that recompile as a map of moment-dominance network statements: from any
QH-network witnessing `BitNetMomStmtG` at `Jain.bitR7plain`, one obtains a (possibly different)
QH-network witnessing the same statement at `Jain.bitR8`. -/
theorem oppbank_mom_of_plain :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain →
      BitNetMomStmtG 104719230 529 Jain.bitR8 := by
  sorry

end IntMul.Kappa.R8.Bit
