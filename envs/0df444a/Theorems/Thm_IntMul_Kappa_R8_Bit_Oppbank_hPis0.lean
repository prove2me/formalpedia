-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0
-- name    : IntMul.Kappa.R8.Bit.Oppbank.hPis0
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:04:59.500969+00:00
-- url     : https://prove2.me/theorems/80e04156-7d7b-406f-aeda-264d317f65fa
-- title:
--   Every densified Pis0 projector is idempotent
-- statement:
--   For the densified opp-bank idempotent set
--
--   $$\mathrm{Pis0}=\{\mathrm{Dm}(o,c):(o,c)\in\mathrm{idxD}\}\cup\{\mathrm{Pl}(b):b<1771\},$$
--
--   every matrix $A\in\mathrm{Pis0}$ satisfies $A^2=A$.
--
--   Together with NetFB $\mathrm{hLab0}$ this feeds $\mathrm{flagBasis}\,\mathrm{Lab0}\,\mathrm{hLab0}\,\mathrm{Pis0}\,\mathrm{hPis0}$ to discharge full $\mathrm{FB0\_ex}$.
-- source:
--   Defs52 Pis0; MoveFacts3 Pc_idem/Dm_idem_*; NetFB Pl_idem; PndIdem

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem hPis0 : ∀ A ∈ Pis0, A * A = A := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
