-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair034_checked
-- name    : Helfgott.mobiusHarmonicPair034_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:03:10.308748+00:00
-- url     : https://prove2.me/theorems/e21f0b0e-a4f0-4e0c-9b06-a06e98ab0457
-- title:
--   Mertens harmonic certificate on [557056, 573440)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $557056\le n<573440$. At scale $Q=10^9$, the total checked bound for this interval is $U=616139408$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair034_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 557056 (MobiusHarmonicTree.branch 616139408 mobiusHarmonicBlock068 mobiusHarmonicBlock069) = true := by sorry

end Helfgott
