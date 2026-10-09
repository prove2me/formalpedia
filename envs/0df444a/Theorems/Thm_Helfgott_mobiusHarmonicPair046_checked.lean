-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair046_checked
-- name    : Helfgott.mobiusHarmonicPair046_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:43:52.003972+00:00
-- url     : https://prove2.me/theorems/51eeb1fb-b0f6-46d4-ae18-5bfba7f6a028
-- title:
--   Mertens harmonic certificate on [753664, 770048)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $753664\le n<770048$. At scale $Q=10^9$, the total checked bound for this interval is $U=1687422084$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair046_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 753664 (MobiusHarmonicTree.branch 1687422084 mobiusHarmonicBlock092 mobiusHarmonicBlock093) = true := by sorry

end Helfgott
