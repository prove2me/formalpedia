-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_PE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_PE
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:24:47.719537+00:00
-- url     : https://prove2.me/theorems/ede46fb0-01ed-4fef-b889-d20e5c0c7790
-- title:
--   PE inhabitance for en (oneRun 484)
-- statement:
--   Data-entrance edges: for $a,t<v$, $K(S_0,S_0^{-1},1-P_\ell(a),1-P_\ell(t))$ realises `oneRun 484` ($=m-2h+1$).
--
--   Matches Jain `onerun_hist` bin width $484$ with multiplicity $2N$.
--
--   **Formalization Note.** Uses OneRunPE2 `oneRun_of_pivs` at $r=484$.
-- source:
--   OneRun2; OneRunPE2; width_en

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem net0O2_en_PE (a t : ℕ) (ha : a < v) (ht : t < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484) e := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
