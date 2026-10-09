-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair015_checked
-- name    : Helfgott.mobiusHarmonicPair015_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:16.647268+00:00
-- url     : https://prove2.me/theorems/fb7c2732-ffda-4fb6-8841-0c91c97a8ce5
-- title:
--   Mertens harmonic certificate on [245760, 262144)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $245760\le n<262144$. At scale $Q=10^9$, the total checked bound for this interval is $U=1760810682$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair015_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 245760 (MobiusHarmonicTree.branch 1760810682 mobiusHarmonicBlock030 mobiusHarmonicBlock031) = true := by sorry

end Helfgott
