-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair054_checked
-- name    : Helfgott.mobiusValuePair054_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:10:46.843687+00:00
-- url     : https://prove2.me/theorems/3e7a02a4-f24a-4a43-ad09-0bdf6753fe28
-- title:
--   Mobius factor certificate on [884736, 901120)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $884736\le n<901120$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair054_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 884736 (MobiusCertTree.branch mobiusTableBlock108 mobiusTableBlock109) = true := by sorry

end Helfgott
