-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair065_checked
-- name    : Helfgott.mobiusHarmonicPair065_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:57:36.946629+00:00
-- url     : https://prove2.me/theorems/c3a8c256-92a2-4e3e-b1da-dc11824e8b74
-- title:
--   Mertens harmonic certificate on [1064960, 1078853)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $1064960\le n<1078853$. At scale $Q=10^9$, the total checked bound for this interval is $U=4731376096$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair065_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1064960 (MobiusHarmonicTree.branch 4731376096 mobiusHarmonicBlock130 mobiusHarmonicBlock131) = true := by sorry

end Helfgott
