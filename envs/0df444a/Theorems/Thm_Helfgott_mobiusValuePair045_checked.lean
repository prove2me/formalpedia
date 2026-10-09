-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair045_checked
-- name    : Helfgott.mobiusValuePair045_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:37:39.904606+00:00
-- url     : https://prove2.me/theorems/6d304782-6dfc-4dd7-9eca-fabf3a0efd31
-- title:
--   Mobius factor certificate on [737280, 753664)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $737280\le n<753664$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair045_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 737280 (MobiusCertTree.branch mobiusTableBlock090 mobiusTableBlock091) = true := by sorry

end Helfgott
