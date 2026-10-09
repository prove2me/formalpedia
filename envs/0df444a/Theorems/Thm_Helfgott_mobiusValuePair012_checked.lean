-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair012_checked
-- name    : Helfgott.mobiusValuePair012_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:33:58.537015+00:00
-- url     : https://prove2.me/theorems/201f7436-5d74-4e54-a975-31a9bfa4a83e
-- title:
--   Mobius factor certificate on [196608, 212992)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $196608\le n<212992$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair012_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 196608 (MobiusCertTree.branch mobiusTableBlock024 mobiusTableBlock025) = true := by sorry

end Helfgott
