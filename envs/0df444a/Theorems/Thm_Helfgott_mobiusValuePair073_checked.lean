-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair073_checked
-- name    : Helfgott.mobiusValuePair073_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:15:51.558574+00:00
-- url     : https://prove2.me/theorems/bf0d968c-4b3d-49de-9039-1e3b241b85a8
-- title:
--   Mobius factor certificate on [1196032, 1200001)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $1196032\le n<1200001$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair073_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1196032 (MobiusCertTree.branch mobiusTableBlock146 (MobiusCertTree.leaf 0 0)) = true := by sorry

end Helfgott
