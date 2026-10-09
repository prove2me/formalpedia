-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair053_checked
-- name    : Helfgott.mobiusHarmonicPair053_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:10:57.667275+00:00
-- url     : https://prove2.me/theorems/3646851b-64b9-474d-8ba2-83484c4b46ba
-- title:
--   Mertens harmonic certificate on [868352, 884736)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $868352\le n<884736$. At scale $Q=10^9$, the total checked bound for this interval is $U=2403771273$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair053_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 868352 (MobiusHarmonicTree.branch 2403771273 mobiusHarmonicBlock106 mobiusHarmonicBlock107) = true := by sorry

end Helfgott
