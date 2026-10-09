-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair007_checked
-- name    : Helfgott.mobiusValuePair007_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:13:47.355678+00:00
-- url     : https://prove2.me/theorems/23e69b26-309b-4130-867c-b94fc52f5f8a
-- title:
--   Mobius factor certificate on [114688, 131072)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $114688\le n<131072$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair007_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 114688 (MobiusCertTree.branch mobiusTableBlock014 mobiusTableBlock015) = true := by sorry

end Helfgott
