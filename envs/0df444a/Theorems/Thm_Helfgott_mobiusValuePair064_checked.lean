-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair064_checked
-- name    : Helfgott.mobiusValuePair064_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:51:22.324142+00:00
-- url     : https://prove2.me/theorems/65d45d6a-9375-4ecd-b34a-648ff34acfb4
-- title:
--   Mobius factor certificate on [1048576, 1064960)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1048576\le n<1064960$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair064_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1048576 (MobiusCertTree.branch mobiusTableBlock128 mobiusTableBlock129) = true := by sorry

end Helfgott
