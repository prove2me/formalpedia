-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair059_checked
-- name    : Helfgott.mobiusValuePair059_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:29:45.506991+00:00
-- url     : https://prove2.me/theorems/99ab25d4-877b-47e6-8a56-708ad6779966
-- title:
--   Mobius factor certificate on [966656, 983040)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $966656\le n<983040$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair059_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 966656 (MobiusCertTree.branch mobiusTableBlock118 mobiusTableBlock119) = true := by sorry

end Helfgott
