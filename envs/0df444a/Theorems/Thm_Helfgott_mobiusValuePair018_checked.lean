-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair018_checked
-- name    : Helfgott.mobiusValuePair018_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:56:14.834567+00:00
-- url     : https://prove2.me/theorems/bdc3f900-3b67-4a1a-8713-c52c52228214
-- title:
--   Mobius factor certificate on [294912, 311296)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $294912\le n<311296$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair018_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 294912 (MobiusCertTree.branch mobiusTableBlock036 mobiusTableBlock037) = true := by sorry

end Helfgott
