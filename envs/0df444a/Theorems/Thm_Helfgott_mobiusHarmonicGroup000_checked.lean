-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicGroup000_checked
-- name    : Helfgott.mobiusHarmonicGroup000_checked
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-08T21:21:25.589903+00:00
-- url     : https://prove2.me/theorems/0a4eeff8-82c9-4cf8-99b7-7a300e1632c6
-- title:
--   Mertens harmonic certificate on [0, 32768)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $0\le n<32768$. At scale $Q=10^9$, the total checked bound for this interval is $U=57637715881$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicGroup000_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 10 0 mobiusHarmonicGroup000 = true := by sorry

end Helfgott
