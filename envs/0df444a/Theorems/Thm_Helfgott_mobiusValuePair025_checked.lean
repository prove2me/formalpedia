-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair025_checked
-- name    : Helfgott.mobiusValuePair025_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:25:44.325395+00:00
-- url     : https://prove2.me/theorems/ebc74be7-b537-4d52-91b7-bff06779dd4f
-- title:
--   Mobius factor certificate on [409600, 425984)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $409600\le n<425984$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair025_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 409600 (MobiusCertTree.branch mobiusTableBlock050 mobiusTableBlock051) = true := by sorry

end Helfgott
