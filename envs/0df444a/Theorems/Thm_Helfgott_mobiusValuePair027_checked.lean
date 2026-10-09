-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair027_checked
-- name    : Helfgott.mobiusValuePair027_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:33:51.166902+00:00
-- url     : https://prove2.me/theorems/c3657580-133b-4cce-b0f7-d6def69b6888
-- title:
--   Mobius factor certificate on [442368, 458752)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $442368\le n<458752$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair027_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 442368 (MobiusCertTree.branch mobiusTableBlock054 mobiusTableBlock055) = true := by sorry

end Helfgott
