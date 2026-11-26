-- Prove2me | Theorems.Thm_HMBinPacking_lenstra_clear_denominators
-- name    : HMBinPacking.lenstra_clear_denominators
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:58:48.273618+00:00
-- url     : https://prove2.me/theorems/7fdb4137-8336-4a68-a3da-d0bfb4136e26
-- title:
--   Lemma 7, denominator clearing with a quadratic binary encoding bound
-- statement:
--   For any high-multiplicity bin packing instance I, residue vector r, and rational objective u, there are a positive integer q and an integer vector w with q u = w. In the registered binary encoding, the full integer-program data consisting of d, the size vector, the capacity, r, and w uses at most (d + L + ℓ)² bits, where L is the instance code length and ℓ is the objective code length.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Proof of Lemma 7, p.5. The arithmetic or geometric subclaim in the proof of Lemma 7.

import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Finset HMBinPacking
open ExponomialAssortment.FPTAS

namespace HMBinPacking

theorem lenstra_clear_denominators (I : Instance) (r : Fin I.d → Fin I.d) (u : Fin I.d → ℚ) :
    ∃ (q : ℕ) (w : Fin I.d → ℤ), 0 < q ∧ (∀ i, (q : ℚ) * u i = (w i : ℚ)) ∧
      (encodeNat I.d ++ encodeNatVec I.s ++ encodeNat I.B ++ encodeResidue r ++
        encodeIntVec w).length ≤ (I.d + inputLength I + (encVec u).length) ^ 2 := by sorry

end HMBinPacking
