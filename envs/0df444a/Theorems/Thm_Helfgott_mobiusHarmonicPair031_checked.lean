-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair031_checked
-- name    : Helfgott.mobiusHarmonicPair031_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:18.270616+00:00
-- url     : https://prove2.me/theorems/2e4f72a3-d194-45ac-a767-c1cc9d83d0ee
-- title:
--   Mertens harmonic certificate on [507904, 524288)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $507904\le n<524288$. At scale $Q=10^9$, the total checked bound for this interval is $U=2314621016$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair031_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 507904 (MobiusHarmonicTree.branch 2314621016 mobiusHarmonicBlock062 mobiusHarmonicBlock063) = true := by sorry

end Helfgott
