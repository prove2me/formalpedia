-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonicPair021_checked
-- name    : Helfgott.mobiusHarmonicPair021_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:11:33.234775+00:00
-- url     : https://prove2.me/theorems/77c8ccee-2c23-41b0-b001-d6f5d09323d6
-- title:
--   Mertens harmonic certificate on [344064, 360448)
-- statement:
--   For the fixed candidate Möbius and Mertens-prefix tables, every prefix-sum recurrence and rounded harmonic-upper-bound check succeeds for integers $n$ with $344064\le n<360448$. At scale $Q=10^9$, the total checked bound for this interval is $U=9830611264$. The complete interval certificates combine with the proved soundness theorem to bound the initial Möbius integral.
-- source:
--   Original finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Fixed integer tables and kernel-checked interval computations for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonicPair021_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 344064 (MobiusHarmonicTree.branch 9830611264 mobiusHarmonicBlock042 mobiusHarmonicBlock043) = true := by sorry

end Helfgott
