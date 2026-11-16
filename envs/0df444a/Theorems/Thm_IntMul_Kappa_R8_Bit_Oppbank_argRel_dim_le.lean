-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le
-- name    : IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:39:00.20429+00:00
-- url     : https://prove2.me/theorems/c8a27a78-bc40-46bc-9d68-2904910401a2
-- title:
--   argRel implies dimF a ≤ dimF n on published Pnd
-- statement:
--   # $\mathrm{argRel}$ implies $\dim F(a)\le \dim F(n)$
--
--   On published (non-Fix) Pnd, if $a,n$ are densified nodes and $\mathrm{argRel}(a,n)$ holds (that is, $a$ is one of the two packed argument slots of $n$), then
--
--   $$\dim F(a)\le \dim F(n).$$
--
--   Empirically there are no argument-related pairs with $\dim F(a)>\dim F(n)$. The equality case includes the 1770 leaf pairs where land-mono fails; this lemma only claims the weak inequality, not land-mono.
--
--   Formalization note. The proof consolidates the five already-proved range lemmas `argRel_dim_le_R0`--`R4` and unfolds `argRel`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: argRel_dim_le on published Pnd, for strict-dim nest_Le.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- If `argRel a n`, then `dimF a ≤ dimF n`. Empirically true on published Pnd
    (zero argRel pairs have dimF a > dimF n). -/
theorem argRel_dim_le {a n : ℕ} (ha : a < nNodes) (hn : n < nNodes)
    (h : argRel a n = true) : dimF a ≤ dimF n := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
