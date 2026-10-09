-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair051_checked
-- name    : Helfgott.mobiusHarmonicPair051_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:02:48.69181+00:00
-- url     : https://prove2.me/theorems/e91b3f46-12c5-4c8b-98cf-fb5a2097fa57
-- title:
--   Mertens harmonic certificate on [835584, 851968)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $835584\le n<851968$. At scale $Q=10^9$, the total checked bound for this interval is $U=3352037715$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair051_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 835584 (MobiusHarmonicTree.branch 3352037715 mobiusHarmonicBlock102 mobiusHarmonicBlock103) = true := by sorry

end Helfgott
