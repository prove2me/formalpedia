-- Prove2me | Theorems.Thm_HardyFLocal_clump_coordinate_equivalence
-- name    : HardyFLocal.clump_coordinate_equivalence
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:01:38.266732+00:00
-- url     : https://prove2.me/theorems/d3458887-1529-4025-a013-5ccf49698d5e
-- title:
--   Clump labels are freely indexed at the starts of wire runs
-- statement:
--   The actual finset of fiducial clump labels is in bijection with independent choices of a one-qubit index at each clump start, distinguishing the two wires at a crossing. The forward bijection reads the actual decoded fiducial value at each start.
-- source:
--   Hardy, arXiv:0804.0054, section 5, clumping steps 1 and 2.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem clump_coordinate_equivalence {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (O : Finset (X m n)) :
    ∃ e : omegaC L O ≃ ({i : O × Bool // IsClumpStart O
      (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val} → Ω),
      ∀ k i, e k i = (if i.val.2 then (famPairs L O k.val i.val.1.val).1
        else (famPairs L O k.val i.val.1.val).2) := by sorry

end HardyFLocal
