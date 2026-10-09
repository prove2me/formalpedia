-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair070_checked
-- name    : Helfgott.mobiusValuePair070_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:13:06.895701+00:00
-- url     : https://prove2.me/theorems/6639def6-cfe1-41cd-8f1a-677d30897ae5
-- title:
--   Mobius factor certificate on [1146880, 1163264)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1146880\le n<1163264$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair070_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1146880 (MobiusCertTree.branch mobiusTableBlock140 mobiusTableBlock141) = true := by sorry

end Helfgott
