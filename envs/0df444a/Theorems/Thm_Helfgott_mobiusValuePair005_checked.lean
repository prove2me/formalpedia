-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair005_checked
-- name    : Helfgott.mobiusValuePair005_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:06:53.931342+00:00
-- url     : https://prove2.me/theorems/8a40617e-d49b-42d1-90af-42f55e8c5609
-- title:
--   Mobius factor certificate on [81920, 98304)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $81920\le n<98304$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair005_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 81920 (MobiusCertTree.branch mobiusTableBlock010 mobiusTableBlock011) = true := by sorry

end Helfgott
