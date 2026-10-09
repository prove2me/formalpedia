-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair060_checked
-- name    : Helfgott.mobiusValuePair060_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:34:54.087245+00:00
-- url     : https://prove2.me/theorems/be4b4350-2336-45c8-be64-a6ded2debd8c
-- title:
--   Mobius factor certificate on [983040, 999424)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $983040\le n<999424$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair060_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 983040 (MobiusCertTree.branch mobiusTableBlock120 mobiusTableBlock121) = true := by sorry

end Helfgott
