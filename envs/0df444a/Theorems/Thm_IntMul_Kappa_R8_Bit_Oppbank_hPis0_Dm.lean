-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0_Dm
-- name    : IntMul.Kappa.R8.Bit.Oppbank.hPis0_Dm
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:09:00.729409+00:00
-- url     : https://prove2.me/theorems/12d7aeb5-4964-42d5-baa2-4ff225e23e8a
-- title:
--   Densified Dm images in Pis0 are idempotent
-- statement:
--   Every densified move projector in the $\mathrm{idxD}$-image is idempotent:
--
--   $$\forall A\in\mathrm{idxD}.\mathrm{image}\,\mathrm{Dm},\quad A^2=A.$$
--
--   Combined with MoveFacts2 $\mathrm{hPis0\_Pl}$ this yields full $\mathrm{hPis0}$.
-- source:
--   MoveFacts3 Dm_idem_*; R6 move_facts; nest_sound

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem hPis0_Dm :
    ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
