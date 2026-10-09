-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair020_checked
-- name    : Helfgott.mobiusValuePair020_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:03:42.131981+00:00
-- url     : https://prove2.me/theorems/6f2ee7b3-0907-4b5d-9428-1393f5828d57
-- title:
--   Mobius factor certificate on [327680, 344064)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $327680\le n<344064$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair020_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 327680 (MobiusCertTree.branch mobiusTableBlock040 mobiusTableBlock041) = true := by sorry

end Helfgott
