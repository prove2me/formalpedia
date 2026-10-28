-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hasCentre_of_centredStar
-- name    : IntMul.Kappa.R8.Bit.Oppbank.hasCentre_of_centredStar
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:44:19.630858+00:00
-- url     : https://prove2.me/theorems/88bece70-7b95-4847-b371-64e70cd2c0e3
-- title:
--   centredStar implies HasCentre
-- statement:
--   # Star-land certificate implies HasCentre
--
--   Let $\mathrm{sup}$ be a support mask and $c<23$ a centre index. Write $\mathrm{centredStar}(\mathrm{sup},c)$ for the Boolean assertion that $\mathrm{sup}$ is contained in the star of $c$:
--   $$
--   \mathrm{sup}\ \land\ \mathrm{starC}\,c = \mathrm{sup}.
--   $$
--   Assume also that every set bit index of $\mathrm{sup}$ is strictly less than $1771$. Then
--   $$
--   \mathrm{HasCentre}(\mathrm{sup})
--   $$
--   holds with witness $c$: each triple in the support contains $c$, and (by NetFB) every triple has rational weight $3$.
-- source:
--   R8 BitOppbank densified HasCentre / AllDensCentred

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Cent
namespace IntMul.Kappa.R8.Bit.Oppbank

theorem hasCentre_of_centredStar {sup c : ℕ} (hc : c < 23)
    (h : centredStar sup c = true)
    (hbnd : ∀ i, (sup.testBit i = true) → i < 1771) :
    HasCentre sup := by sorry
