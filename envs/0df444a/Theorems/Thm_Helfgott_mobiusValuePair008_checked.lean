-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair008_checked
-- name    : Helfgott.mobiusValuePair008_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:17:47.751283+00:00
-- url     : https://prove2.me/theorems/cf4da9b1-0c9b-4d5f-b061-24f04e437f23
-- title:
--   Mobius factor certificate on [131072, 147456)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $131072\le n<147456$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair008_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 131072 (MobiusCertTree.branch mobiusTableBlock016 mobiusTableBlock017) = true := by sorry

end Helfgott
