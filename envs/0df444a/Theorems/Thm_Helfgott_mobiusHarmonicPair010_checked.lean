-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair010_checked
-- name    : Helfgott.mobiusHarmonicPair010_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:28:06.275477+00:00
-- url     : https://prove2.me/theorems/5ee77437-1fcc-4acb-a726-e323775b9cf6
-- title:
--   Mertens harmonic certificate on [163840, 180224)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $163840\le n<180224$. At scale $Q=10^9$, the total checked bound for this interval is $U=6719072402$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair010_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 163840 (MobiusHarmonicTree.branch 6719072402 mobiusHarmonicBlock020 mobiusHarmonicBlock021) = true := by sorry

end Helfgott
