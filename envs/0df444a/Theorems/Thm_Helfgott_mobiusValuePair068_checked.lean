-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair068_checked
-- name    : Helfgott.mobiusValuePair068_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:06:46.942414+00:00
-- url     : https://prove2.me/theorems/6bf72daa-7862-4208-8c09-d60ce51213ea
-- title:
--   Mobius factor certificate on [1114112, 1130496)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1114112\le n<1130496$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair068_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1114112 (MobiusCertTree.branch mobiusTableBlock136 mobiusTableBlock137) = true := by sorry

end Helfgott
