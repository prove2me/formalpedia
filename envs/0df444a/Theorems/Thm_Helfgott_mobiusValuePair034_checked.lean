-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair034_checked
-- name    : Helfgott.mobiusValuePair034_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:59:04.817793+00:00
-- url     : https://prove2.me/theorems/d6c34eb3-5fb9-4a3b-ad55-6dd5c7326c33
-- title:
--   Mobius factor certificate on [557056, 573440)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $557056\le n<573440$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair034_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 557056 (MobiusCertTree.branch mobiusTableBlock068 mobiusTableBlock069) = true := by sorry

end Helfgott
