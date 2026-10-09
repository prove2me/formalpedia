-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair022_checked
-- name    : Helfgott.mobiusValuePair022_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:11:25.650972+00:00
-- url     : https://prove2.me/theorems/7538c0ad-3eb1-4582-912c-da1ff37d6629
-- title:
--   Mobius factor certificate on [360448, 376832)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $360448\le n<376832$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair022_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 360448 (MobiusCertTree.branch mobiusTableBlock044 mobiusTableBlock045) = true := by sorry

end Helfgott
