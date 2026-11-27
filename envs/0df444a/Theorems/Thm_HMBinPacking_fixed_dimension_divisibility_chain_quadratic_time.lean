-- Prove2me | Theorems.Thm_HMBinPacking_fixed_dimension_divisibility_chain_quadratic_time
-- name    : HMBinPacking.fixed_dimension_divisibility_chain_quadratic_time
-- status  : Open
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:49:11.637089+00:00
-- url     : https://prove2.me/theorems/e03898af-37a8-5234-861a-a9df743291c3
-- title:
--   Quadratic time for divisibility chains in every fixed dimension
-- statement:
--   For each positive fixed dimension n there is one ordinary multistack TM2 and a constant C such that the machine decides all binary-encoded bin packing instances with n types whose sizes form a divisibility chain. It halts within C times (inputLength+1)^2 steps. Input capacity, sizes, multiplicities, and number of bins are unrestricted. The program and constant may depend on n.
-- source:
--   Koana and Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2. Specialized machine theorem in the bit model of the paper.

import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.Linarith
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_HMBinPacking_Instance
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem HMBinPacking.fixed_dimension_divisibility_chain_quadratic_time :
    ∀ n:ℕ, 0<n → ∃ (M:Turing.TM2ComputableAux Bool Bool) (C:ℕ), ∀ I:Instance, I.d=n →
      (∀ i j,I.s i∣I.s j ∨ I.s j∣I.s i) →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (C*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (C*(inputLength I+1)^2)) := by sorry
