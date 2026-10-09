-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair058_checked
-- name    : Helfgott.mobiusValuePair058_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:27:09.598483+00:00
-- url     : https://prove2.me/theorems/962ba5d0-89d9-4161-b903-f01e3883e0a1
-- title:
--   Mobius factor certificate on [950272, 966656)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $950272\le n<966656$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair058_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 950272 (MobiusCertTree.branch mobiusTableBlock116 mobiusTableBlock117) = true := by sorry

end Helfgott
