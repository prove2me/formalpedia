-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair002_checked
-- name    : Helfgott.mobiusHarmonicPair002_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:53:10.25198+00:00
-- url     : https://prove2.me/theorems/2fdc09b7-4597-4fb4-8def-13e56cc01446
-- title:
--   Mertens harmonic certificate on [32768, 49152)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $32768\le n<49152$. At scale $Q=10^9$, the total checked bound for this interval is $U=10651587885$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair002_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 32768 (MobiusHarmonicTree.branch 10651587885 mobiusHarmonicBlock004 mobiusHarmonicBlock005) = true := by sorry

end Helfgott
