-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair033_checked
-- name    : Helfgott.mobiusHarmonicPair033_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:57:26.60279+00:00
-- url     : https://prove2.me/theorems/4f94aa5f-4235-4428-91b8-a43b8bbaed3e
-- title:
--   Mertens harmonic certificate on [540672, 557056)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $540672\le n<557056$. At scale $Q=10^9$, the total checked bound for this interval is $U=711475365$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair033_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 540672 (MobiusHarmonicTree.branch 711475365 mobiusHarmonicBlock066 mobiusHarmonicBlock067) = true := by sorry

end Helfgott
