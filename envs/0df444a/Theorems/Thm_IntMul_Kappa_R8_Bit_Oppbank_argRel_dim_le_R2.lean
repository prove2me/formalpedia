-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R2
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:36:19.332207+00:00
-- url     : https://prove2.me/theorems/f598909d-71ee-4e8b-890c-ec9eb8aa78cd
-- title:
--   argRel dim inequality certificates on published Pnd, nodes 25000–37499
-- statement:
--   # $\mathrm{argRel}$ dimension inequality, region $R_2$
--
--   For every densified node $n$ with $25000\le n<37500$, both argument slots satisfy
--   $\dim F(\mathrm{arg}_0 n)\le \dim F(n)$ and $\dim F(\mathrm{arg}_1 n)\le \dim F(n)$, where $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$.
--
--   These are intermediate range lemmas for `argRel_dim_le` ($\mathrm{argRel}(a,n)$ implies $\dim F(a)\le \dim F(n)$) on published (non-Fix) Pnd.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: range consolidator for argRel_dim_le on published Pnd.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- Dim inequality for both argument slots on nodes in [25000, 37500). -/
theorem argRel_dim_le_R2 (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 37500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
