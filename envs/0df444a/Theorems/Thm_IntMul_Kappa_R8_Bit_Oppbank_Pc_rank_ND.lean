-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank_ND
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:16:09.428896+00:00
-- url     : https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d
-- title:
--   ND code: rank PndD = dimF
-- statement:
--   For densified ND codes $c=1773+n<codeBound$ with a centre, $\mathrm{rank}(\mathrm{Pc}\,c)=\mathrm{dimF}\,n$.
-- source:
--   R6 nd_facts / Pnd_rank + dim table

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
theorem Pc_rank_ND {n : ℕ} (hn : 1773 + n < codeBound)
    (hC : HasCentre (densSupG n)) :
    (Pc (1773 + n)).rank = dimF n := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
