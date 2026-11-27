-- Prove2me | Theorems.Thm_HMBinPacking_two_types_large_singleton_or_chain_quadratic_time
-- name    : HMBinPacking.two_types_large_singleton_or_chain_quadratic_time
-- status  : Open
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:50:18.397383+00:00
-- url     : https://prove2.me/theorems/a4dd7706-551c-4d04-96aa-e25419dee5dc
-- title:
--   Quadratic time for two item types with a large type, a singleton type or comparable sizes
-- statement:
--   One fixed, ordinary multistack TM2 decides every instance with exactly two types and a type whose size strictly exceeds half the capacity or whose total multiplicity is at most one, as well as every two-type instance in which either item size divides the other. The capacity need not be divisible by the sizes. Both truth values halt on the registered binary input in at most C (inputLength+1)^2 actual steps for one universal constant C. Capacities, multiplicities and the number of bins have no other restriction. The qualifying type can appear in either input position.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Definitions.Def_HMBinPacking_Instance
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem HMBinPacking.two_types_large_singleton_or_chain_quadratic_time :
    ∃ (M:Turing.TM2ComputableAux Bool Bool) (C:ℕ), ∀ I:Instance, I.d=2 → ((∃ j,I.B<2*I.s j ∨ I.a j≤1) ∨ (∀ i j,I.s i∣I.s j ∨ I.s j∣I.s i)) →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (C*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (C*(inputLength I+1)^2)) := by sorry
