-- Prove2me | Theorems.Thm_HMBinPacking_divisibility_chain_or_one_bin_quadratic_time
-- name    : HMBinPacking.divisibility_chain_or_one_bin_quadratic_time
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:46:41.240267+00:00
-- url     : https://prove2.me/theorems/7085bd9f-af98-4f21-a21e-426bfeb88dbf
-- title:
--   Quadratic deterministic bit time for divisibility chains and arbitrary one-bin instances
-- statement:
--   A single deterministic Boolean TM2 decides feasibility of every original instance with one bin, and every instance whose item sizes are pairwise comparable by divisibility and each divide the capacity. Its time bound is 500(L+1)^2 for the original binary length L. The number and ordering of types, multiplicities and the bin count can vary in the divisibility-chain case.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Instance
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem HMBinPacking.divisibility_chain_or_one_bin_quadratic_time :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ I : Instance,
      (I.b=1 ∨ ((∀ i j, I.s i ∣ I.s j ∨ I.s j ∣ I.s i) ∧ (∀ i, I.s i ∣ I.B))) →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (500*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (500*(inputLength I+1)^2)) := by sorry
