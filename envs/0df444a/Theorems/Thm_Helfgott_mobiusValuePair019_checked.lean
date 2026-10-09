-- Prove2me | Theorems.Thm_Helfgott_mobiusValuePair019_checked
-- name    : Helfgott.mobiusValuePair019_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:02:29.35711+00:00
-- url     : https://prove2.me/theorems/bfb466d4-cded-4577-92f1-ff0395fed897
-- title:
--   Mobius factor certificate on [311296, 327680)
-- statement:
--   For the fixed candidate Möbius table through 1200000, every prime-flag, prime-factor and Möbius recurrence check succeeds for integers $n$ with $311296\le n<327680$. These are finite arithmetic checks; with the other interval certificates and the proved soundness theorem, they identify the complete candidate table with the Möbius function.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusValuePair019_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 311296 (MobiusCertTree.branch mobiusTableBlock038 mobiusTableBlock039) = true := by sorry

end Helfgott
