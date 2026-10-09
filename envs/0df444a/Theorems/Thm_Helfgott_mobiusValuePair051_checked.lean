-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair051_checked
-- name    : Helfgott.mobiusValuePair051_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:59:52.189719+00:00
-- url     : https://prove2.me/theorems/6937713a-54ac-46cf-b090-7d9e1b99daa5
-- title:
--   Mobius factor certificate on [835584, 851968)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $835584\le n<851968$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair051_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 835584 (MobiusCertTree.branch mobiusTableBlock102 mobiusTableBlock103) = true := by sorry

end Helfgott
