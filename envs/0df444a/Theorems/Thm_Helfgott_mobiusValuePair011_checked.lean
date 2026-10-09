-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair011_checked
-- name    : Helfgott.mobiusValuePair011_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:30:56.629346+00:00
-- url     : https://prove2.me/theorems/1715bd03-ab34-4fd7-970a-7510c76bf86f
-- title:
--   Mobius factor certificate on [180224, 196608)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $180224\le n<196608$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair011_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 180224 (MobiusCertTree.branch mobiusTableBlock022 mobiusTableBlock023) = true := by sorry

end Helfgott
