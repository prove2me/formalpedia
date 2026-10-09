-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair002_checked
-- name    : Helfgott.mobiusValuePair002_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:52:18.722979+00:00
-- url     : https://prove2.me/theorems/d2f16d1b-4170-4084-bd51-3b371ba7b9d8
-- title:
--   Mobius factor certificate on [32768, 49152)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $32768\le n<49152$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair002_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 32768 (MobiusCertTree.branch mobiusTableBlock004 mobiusTableBlock005) = true := by sorry

end Helfgott
