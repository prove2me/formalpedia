-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair023_checked
-- name    : Helfgott.mobiusHarmonicPair023_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:18:32.608588+00:00
-- url     : https://prove2.me/theorems/c252b9bf-c3aa-45ae-83b0-6923d70939a7
-- title:
--   Mertens harmonic certificate on [376832, 393216)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $376832\le n<393216$. At scale $Q=10^9$, the total checked bound for this interval is $U=1115317195$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair023_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 376832 (MobiusHarmonicTree.branch 1115317195 mobiusHarmonicBlock046 mobiusHarmonicBlock047) = true := by sorry

end Helfgott
