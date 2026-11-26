-- Prove2me | Theorems.Thm_HMBinPacking_one_type_quadratic_time
-- name    : HMBinPacking.one_type_quadratic_time
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:22:26.023362+00:00
-- url     : https://prove2.me/theorems/df810d86-2dd6-5d87-93b5-b1b8ed7ea649
-- title:
--   One item type in high-multiplicity bin packing is decidable in quadratic deterministic bit time
-- statement:
--   Specialization of Theorem 1 of Koana and Kumabe to one item type. A single deterministic Boolean multi-stack Turing machine decides every such high-multiplicity bin-packing instance using the original encoding. For binary input length L, it halts with exactly the feasibility bit in at most 200(L+1)^2 steps. The capacity, the positive item size, the multiplicity and the number of bins are all variable.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, Theorem 1, one-type specialization. https://arxiv.org/abs/2609.16923

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Instance
open HMBinPacking

theorem HMBinPacking.one_type_quadratic_time :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ I : Instance, I.d = 1 →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (200*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (200*(inputLength I+1)^2)) := by sorry
