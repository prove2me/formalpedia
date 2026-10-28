-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO2_oneRun_PE_families
-- name    : IntMul.Kappa.R8.Bit.Oppbank.EOKO2_oneRun_PE_families
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:52:32.21199+00:00
-- url     : https://prove2.me/theorems/4db38dac-382c-4ef8-83b6-8aae0e683cbd
-- title:
--   OneRun2 PE inhabitance for densified ch0NB edge families
-- statement:
--   # OneRun2 PE inhabitance
--
--   On the corrected carrier, every densified $\mathrm{EOKO2}$ edge family admits a witness edge under $\mathrm{oneRun}\,r$ (runs $[(0,0,r)]$): nested side, aux (width $22$), data (width $484$), and rank-$1$ side edges.
--
--   **Formalization Note.** Prefer over legacy `EOKO_oneRun_PE_families` (padded `oneRun` is unsatisfiable at rank $r>1$).
-- source:
--   OneRunPE2; EOKOPack2; FB0_ex

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 (PE oneRun)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
theorem EOKO2_oneRun_PE_families :
    (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
    (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
    (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
    (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
