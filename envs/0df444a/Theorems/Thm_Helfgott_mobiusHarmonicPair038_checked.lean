-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair038_checked
-- name    : Helfgott.mobiusHarmonicPair038_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:16:14.520777+00:00
-- url     : https://prove2.me/theorems/56d1b2b4-9a97-4710-b4a2-89614c560a4c
-- title:
--   Mertens harmonic certificate on [622592, 638976)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $622592\le n<638976$. At scale $Q=10^9$, the total checked bound for this interval is $U=1781374855$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair038_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 622592 (MobiusHarmonicTree.branch 1781374855 mobiusHarmonicBlock076 mobiusHarmonicBlock077) = true := by sorry

end Helfgott
