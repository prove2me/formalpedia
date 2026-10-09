-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair049_checked
-- name    : Helfgott.mobiusValuePair049_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:52:51.58876+00:00
-- url     : https://prove2.me/theorems/74dd035b-8cd5-4df7-abe1-a16b8d54698b
-- title:
--   Mobius factor certificate on [802816, 819200)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $802816\le n<819200$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair049_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 802816 (MobiusCertTree.branch mobiusTableBlock098 mobiusTableBlock099) = true := by sorry

end Helfgott
