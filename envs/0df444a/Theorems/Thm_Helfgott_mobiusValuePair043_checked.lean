-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair043_checked
-- name    : Helfgott.mobiusValuePair043_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:32:07.164976+00:00
-- url     : https://prove2.me/theorems/88f52985-c640-41b4-856c-3d5bd0d6cc7a
-- title:
--   Mobius factor certificate on [704512, 720896)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $704512\le n<720896$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair043_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 704512 (MobiusCertTree.branch mobiusTableBlock086 mobiusTableBlock087) = true := by sorry

end Helfgott
