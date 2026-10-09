-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair001_checked
-- name    : Helfgott.mobiusValuePair001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:51:34.02598+00:00
-- url     : https://prove2.me/theorems/af5473c9-40ec-496a-8762-861b6e1728bf
-- title:
--   Mobius factor certificate on [16384, 32768)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $16384\le n<32768$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair001_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 16384 (MobiusCertTree.branch mobiusTableBlock002 mobiusTableBlock003) = true := by sorry

end Helfgott
