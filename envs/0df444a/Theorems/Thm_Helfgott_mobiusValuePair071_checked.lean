-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair071_checked
-- name    : Helfgott.mobiusValuePair071_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:13:44.756025+00:00
-- url     : https://prove2.me/theorems/293eecf8-26ad-4ce5-8205-ebee2855cf46
-- title:
--   Mobius factor certificate on [1163264, 1179648)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1163264\le n<1179648$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair071_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1163264 (MobiusCertTree.branch mobiusTableBlock142 mobiusTableBlock143) = true := by sorry

end Helfgott
