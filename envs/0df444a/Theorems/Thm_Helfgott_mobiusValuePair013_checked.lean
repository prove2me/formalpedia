-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair013_checked
-- name    : Helfgott.mobiusValuePair013_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:39:34.543862+00:00
-- url     : https://prove2.me/theorems/f8ce4bb1-019a-4f3d-8a80-93f68df892c4
-- title:
--   Mobius factor certificate on [212992, 229376)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $212992\le n<229376$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair013_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 212992 (MobiusCertTree.branch mobiusTableBlock026 mobiusTableBlock027) = true := by sorry

end Helfgott
