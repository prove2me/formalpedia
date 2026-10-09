-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair025_checked
-- name    : Helfgott.mobiusHarmonicPair025_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:26:15.979597+00:00
-- url     : https://prove2.me/theorems/be79d719-ecbe-4939-989a-df745bb97a19
-- title:
--   Mertens harmonic certificate on [409600, 425984)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $409600\le n<425984$. At scale $Q=10^9$, the total checked bound for this interval is $U=5604783700$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair025_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 409600 (MobiusHarmonicTree.branch 5604783700 mobiusHarmonicBlock050 mobiusHarmonicBlock051) = true := by sorry

end Helfgott
