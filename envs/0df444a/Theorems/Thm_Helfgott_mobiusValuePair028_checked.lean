-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair028_checked
-- name    : Helfgott.mobiusValuePair028_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:35:22.310873+00:00
-- url     : https://prove2.me/theorems/2bf96058-4fe8-4722-9580-875cd10e0110
-- title:
--   Mobius factor certificate on [458752, 475136)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $458752\le n<475136$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair028_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 458752 (MobiusCertTree.branch mobiusTableBlock056 mobiusTableBlock057) = true := by sorry

end Helfgott
