-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair047_checked
-- name    : Helfgott.mobiusValuePair047_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:43:42.588677+00:00
-- url     : https://prove2.me/theorems/7dc75b0c-90c6-433d-b6db-c95affb0e9f0
-- title:
--   Mobius factor certificate on [770048, 786432)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $770048\le n<786432$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair047_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 770048 (MobiusCertTree.branch mobiusTableBlock094 mobiusTableBlock095) = true := by sorry

end Helfgott
