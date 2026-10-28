-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_oneRun_PE_families
-- name    : IntMul.Kappa.R8.Bit.Oppbank.EOKO_oneRun_PE_families
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:16:02.069916+00:00
-- url     : https://prove2.me/theorems/f164aa4e-218f-4a31-a028-a274eded5833
-- title:
--   One-run PE inhabitance for densified ch0NB edge families
-- statement:
--   # One-run PE inhabitance for opp-bank channel edges
--
--   For densified $\mathrm{ch0NB}$, every $\mathrm{EOKO}$ edge family admits a witness edge under the one-run predicate (runs $[(0,0,r)]$): nested side edges, aux edges of width $22$, data edges of width $484$, and rank-$1$ side edges.
--
--   **Formalization Note.** `rkC` from Pnd; `PE`/`oneRun` from OneRunNet; `codeBound` from SupG.
-- source:
--   OneRunPE2; FB0_ex; EOKO edgeMats

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet (PE oneRun)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
theorem EOKO_oneRun_PE_families :
    (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
    (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
    (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
    (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
