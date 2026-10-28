-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_eq_of_Le_dimrev
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pc_eq_of_Le_dimrev
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:04:34.718821+00:00
-- url     : https://prove2.me/theorems/dc0264bc-a760-45fd-a388-966ca7f96ab0
-- title:
--   Le + reverse dim order ⇒ equal densified Pc
-- statement:
--   If densified projectors nest as $\mathrm{Le}(\mathrm{Pc}\,a,\mathrm{Pc}\,b)$ and $\mathrm{dimCF}\,b\le\mathrm{dimCF}\,a$, then $\mathrm{Pc}\,a=\mathrm{Pc}\,b$. Follows from $\mathrm{Pc\_rank}=\mathrm{dimCF}$ together with `le_eq_of_rank`.
-- source:
--   R6 le_eq_of_rank + Pc_rank for Dm_idem_of_Le mismatch branch

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- If Le (Pc a)(Pc b) and dimCF b ≤ dimCF a then Pc a = Pc b. -/
theorem Pc_eq_of_Le_dimrev {a b : ℕ} (ha : a < codeBound) (hb : b < codeBound)
    (hLe : Le (Pc a) (Pc b)) (hdim : dimCF b ≤ dimCF a) :
    Pc a = Pc b := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
