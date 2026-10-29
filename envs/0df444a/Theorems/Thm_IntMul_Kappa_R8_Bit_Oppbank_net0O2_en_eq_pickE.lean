-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_eq_pickE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_eq_pickE
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:05:23.290005+00:00
-- url     : https://prove2.me/theorems/eecebf0c-0bf8-4376-970f-380ecce12ffe
-- title:
--   ch0O.en equals OneRunNet2.pickE of oneRun-484 PE
-- statement:
--   For indices $a,t<v$, the densified entrance child is the classical choice of a width-$484$ one-run PE on the projector pair $(1-P_a,1-P_t)$:
--   $$
--   \mathrm{en}(a,t)=\mathrm{pickE}\bigl(\mathrm{PE}(K(S_0,S_0^{-1},1-P_a,1-P_t),\mathrm{oneRun}\,484)\bigr).
--   $$
--
--   **Formalization Note.** Unfold `ch0O.en` with `OneRunNet2.PE`/`pickE` (not `Pnd.PE`).
-- source:
--   OneRun2 ch0O.en definition

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix
theorem net0O2_en_eq_pickE (a t : ℕ) (ha : a < v) (ht : t < v) :
    ch0O.en a t =
      OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484)) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
