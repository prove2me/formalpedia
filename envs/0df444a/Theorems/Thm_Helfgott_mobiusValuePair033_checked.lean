-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair033_checked
-- name    : Helfgott.mobiusValuePair033_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:57:06.772702+00:00
-- url     : https://prove2.me/theorems/11cdeb36-5123-4ece-9e19-69581a2c2ab8
-- title:
--   Mobius factor certificate on [540672, 557056)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $540672\le n<557056$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair033_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 540672 (MobiusCertTree.branch mobiusTableBlock066 mobiusTableBlock067) = true := by sorry

end Helfgott
