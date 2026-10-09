-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair037_checked
-- name    : Helfgott.mobiusValuePair037_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:11:12.9915+00:00
-- url     : https://prove2.me/theorems/6a4c937f-4666-4f59-8bb3-294ae1764f07
-- title:
--   Mobius factor certificate on [606208, 622592)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $606208\le n<622592$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair037_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 606208 (MobiusCertTree.branch mobiusTableBlock074 mobiusTableBlock075) = true := by sorry

end Helfgott
