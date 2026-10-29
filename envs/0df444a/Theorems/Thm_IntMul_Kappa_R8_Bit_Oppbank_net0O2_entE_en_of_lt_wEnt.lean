-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_en_of_lt_wEnt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_en_of_lt_wEnt
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:58:11.727145+00:00
-- url     : https://prove2.me/theorems/d67cb8a6-1865-4f0a-a1e2-483472aaecef
-- title:
--   entE on w < wEnt equals an en child
-- statement:
--   Whenever the local entrance wire satisfies $w<w_{\mathrm{Ent}}$, the densified entrance selector $\mathrm{entE}(a,w)$ returns an $e_n$ child of stage $a$:
--   $$
--   w<w_{\mathrm{Ent}}\implies \mathrm{entE}(a,w)=\mathrm{en}(a,t)\quad\text{for some }t<v.
--   $$
--   (The two branches $w<v$ and $v\le w<w_{\mathrm{Ent}}$ remint $t=w$ or $t=w-v$.)
--
--   **Formalization Note.** Unfold `NB.entE`; `wEnt=2v`.
-- source:
--   QHNet entE; OneRun2 ch0O.en

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_entE_en_of_lt_wEnt (a w : ℕ) (ha : a < v) (hw : w < wEnt) :
    ∃ t, t < v ∧ NB.entE (toNB ch0O) a w = ch0O.en a t := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
