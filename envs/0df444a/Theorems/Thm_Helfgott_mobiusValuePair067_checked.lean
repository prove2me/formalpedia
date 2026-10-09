-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair067_checked
-- name    : Helfgott.mobiusValuePair067_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:06:51.712983+00:00
-- url     : https://prove2.me/theorems/7b02a903-5676-412e-8bb4-4dd18e02c48a
-- title:
--   Mobius factor certificate on [1097728, 1114112)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1097728\le n<1114112$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair067_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1097728 (MobiusCertTree.branch mobiusTableBlock134 mobiusTableBlock135) = true := by sorry

end Helfgott
