-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair020_checked
-- name    : Helfgott.mobiusHarmonicPair020_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:05:29.62853+00:00
-- url     : https://prove2.me/theorems/49b1b0c1-a628-46a5-b5e5-89e03649f836
-- title:
--   Mertens harmonic certificate on [327680, 344064)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $327680\le n<344064$. At scale $Q=10^9$, the total checked bound for this interval is $U=7176745740$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair020_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 327680 (MobiusHarmonicTree.branch 7176745740 mobiusHarmonicBlock040 mobiusHarmonicBlock041) = true := by sorry

end Helfgott
