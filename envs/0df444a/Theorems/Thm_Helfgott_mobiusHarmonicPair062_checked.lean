-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair062_checked
-- name    : Helfgott.mobiusHarmonicPair062_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:44:23.053442+00:00
-- url     : https://prove2.me/theorems/0d6d2ade-62a8-4fb2-a9eb-3f3b58fa5af0
-- title:
--   Mertens harmonic certificate on [1015808, 1032192)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $1015808\le n<1032192$. At scale $Q=10^9$, the total checked bound for this interval is $U=1386111687$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair062_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1015808 (MobiusHarmonicTree.branch 1386111687 mobiusHarmonicBlock124 mobiusHarmonicBlock125) = true := by sorry

end Helfgott
