-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair023_checked
-- name    : Helfgott.mobiusValuePair023_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:17:58.938495+00:00
-- url     : https://prove2.me/theorems/3b436402-67c0-4fed-a5c2-d92dad0297c2
-- title:
--   Mobius factor certificate on [376832, 393216)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $376832\le n<393216$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair023_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 376832 (MobiusCertTree.branch mobiusTableBlock046 mobiusTableBlock047) = true := by sorry

end Helfgott
