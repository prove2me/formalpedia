-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair036_checked
-- name    : Helfgott.mobiusValuePair036_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:06:08.841191+00:00
-- url     : https://prove2.me/theorems/33bd486a-6315-4ab7-83f6-53b1b0a02438
-- title:
--   Mobius factor certificate on [589824, 606208)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $589824\le n<606208$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair036_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 589824 (MobiusCertTree.branch mobiusTableBlock072 mobiusTableBlock073) = true := by sorry

end Helfgott
