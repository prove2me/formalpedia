-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair055_checked
-- name    : Helfgott.mobiusValuePair055_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:14:32.223933+00:00
-- url     : https://prove2.me/theorems/bb8c2f1c-98f5-4a16-a415-520fd34e5f87
-- title:
--   Mobius factor certificate on [901120, 917504)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $901120\le n<917504$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair055_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 901120 (MobiusCertTree.branch mobiusTableBlock110 mobiusTableBlock111) = true := by sorry

end Helfgott
