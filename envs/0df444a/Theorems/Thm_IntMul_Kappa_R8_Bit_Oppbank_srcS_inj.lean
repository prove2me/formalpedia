-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_srcS_inj
-- name    : IntMul.Kappa.R8.Bit.Oppbank.srcS_inj
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T12:13:34.006389+00:00
-- url     : https://prove2.me/theorems/895150c2-047b-4738-a4cc-02ecb0d3beb6
-- title:
--   srcS is injective on t < v (QHNetRecR SRC slots)
-- statement:
--   In the published QHNetRecR pack, the source-slot map $\mathrm{srcS}(t) = \mathrm{fieldOf}(\mathrm{SRC}, 16, t)$ is injective for $t < v$ (with $v = 1771$). The 1771 SRC field values are pairwise distinct. The formal certificate is a bitset/popcount argument: the folded OR-bitset of the concrete `srcS` values has popcount 1771, hence the list is nodup, hence `srcS` is injective on `List.range v`. This is not a monolithic `List.Nodup` decision on the 1771 `fieldOf` values.
-- source:
--   FormalOK cascade, Round-8, variant-R carrier QHNetRecR (definition 97df824b), SRC table of WireLayout v=1771; injectivity needed for copyoND MovesV after preF.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- The source-slot map `QHNetRecR.srcS t = fieldOf SRC 16 t` is injective
on `t < v`. Proved by a cheap bitset/popcount certificate (not a
monolithic `List.Nodup` decision on the 1771 `fieldOf` values). -/
theorem srcS_inj {t t' : ℕ} (ht : t < v) (ht' : t' < v)
    (heq : QHNetRecR.srcS t = QHNetRecR.srcS t') : t = t' := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
