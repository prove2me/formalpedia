-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair032_checked
-- name    : Helfgott.mobiusValuePair032_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:49.315932+00:00
-- url     : https://prove2.me/theorems/5eac6914-7f78-4da7-95d7-36093671853d
-- title:
--   Mobius factor certificate on [524288, 540672)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $524288\le n<540672$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair032_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 524288 (MobiusCertTree.branch mobiusTableBlock064 mobiusTableBlock065) = true := by sorry

end Helfgott
