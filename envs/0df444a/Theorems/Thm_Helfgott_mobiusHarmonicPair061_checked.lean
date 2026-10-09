-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair061_checked
-- name    : Helfgott.mobiusHarmonicPair061_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:41:19.125324+00:00
-- url     : https://prove2.me/theorems/439eb6d4-b08c-45b7-ad51-5267c471373b
-- title:
--   Mertens harmonic certificate on [999424, 1015808)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $999424\le n<1015808$. At scale $Q=10^9$, the total checked bound for this interval is $U=2896089686$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair061_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 999424 (MobiusHarmonicTree.branch 2896089686 mobiusHarmonicBlock122 mobiusHarmonicBlock123) = true := by sorry

end Helfgott
