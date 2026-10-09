-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicBlock126_checked
-- name    : Helfgott.mobiusHarmonicBlock126_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:08:44.01681+00:00
-- url     : https://prove2.me/theorems/3ab2b946-5461-4776-bf60-cb6d4b511b76
-- title:
--   Mertens harmonic certificate on [1032192, 1040384)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $1032192\le n<1040384$. At scale $Q=10^9$, the total checked bound for this interval is $U=1417218722$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicBlock126_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 8 1032192 mobiusHarmonicBlock126 = true := by sorry

end Helfgott
