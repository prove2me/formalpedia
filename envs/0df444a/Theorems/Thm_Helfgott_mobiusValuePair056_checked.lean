-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair056_checked
-- name    : Helfgott.mobiusValuePair056_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:18:57.91741+00:00
-- url     : https://prove2.me/theorems/7d791528-2f49-4e47-9af6-a4745835cbe8
-- title:
--   Mobius factor certificate on [917504, 933888)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $917504\le n<933888$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair056_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 917504 (MobiusCertTree.branch mobiusTableBlock112 mobiusTableBlock113) = true := by sorry

end Helfgott
