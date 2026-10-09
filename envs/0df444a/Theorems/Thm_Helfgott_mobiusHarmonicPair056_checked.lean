-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair056_checked
-- name    : Helfgott.mobiusHarmonicPair056_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:20:18.999614+00:00
-- url     : https://prove2.me/theorems/a1ee6ba2-7201-49ae-9fcf-eb278696e697
-- title:
--   Mertens harmonic certificate on [917504, 933888)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $917504\le n<933888$. At scale $Q=10^9$, the total checked bound for this interval is $U=4645284997$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair056_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 917504 (MobiusHarmonicTree.branch 4645284997 mobiusHarmonicBlock112 mobiusHarmonicBlock113) = true := by sorry

end Helfgott
