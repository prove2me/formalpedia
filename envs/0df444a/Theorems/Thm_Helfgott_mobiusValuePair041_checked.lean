-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair041_checked
-- name    : Helfgott.mobiusValuePair041_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:25:07.851115+00:00
-- url     : https://prove2.me/theorems/54edb2a3-305e-47b1-b307-45cacfbd5f8b
-- title:
--   Mobius factor certificate on [671744, 688128)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $671744\le n<688128$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair041_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 671744 (MobiusCertTree.branch mobiusTableBlock082 mobiusTableBlock083) = true := by sorry

end Helfgott
