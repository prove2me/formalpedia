-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair039_checked
-- name    : Helfgott.mobiusValuePair039_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:17:39.280783+00:00
-- url     : https://prove2.me/theorems/7ec00bd4-2203-4608-a4d0-727cfdd5ac22
-- title:
--   Mobius factor certificate on [638976, 655360)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $638976\le n<655360$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair039_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 638976 (MobiusCertTree.branch mobiusTableBlock078 mobiusTableBlock079) = true := by sorry

end Helfgott
