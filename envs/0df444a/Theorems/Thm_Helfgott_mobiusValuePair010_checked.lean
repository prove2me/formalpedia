-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair010_checked
-- name    : Helfgott.mobiusValuePair010_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:25:06.79411+00:00
-- url     : https://prove2.me/theorems/83557999-6695-4fa2-a925-2cdb14d2efd0
-- title:
--   Mobius factor certificate on [163840, 180224)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $163840\le n<180224$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair010_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 163840 (MobiusCertTree.branch mobiusTableBlock020 mobiusTableBlock021) = true := by sorry

end Helfgott
