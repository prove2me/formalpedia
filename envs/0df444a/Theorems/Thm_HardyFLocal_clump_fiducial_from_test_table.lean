-- Prove2me | Theorems.Thm_HardyFLocal_clump_fiducial_from_test_table
-- name    : HardyFLocal.clump_fiducial_from_test_table
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:16:20.161618+00:00
-- url     : https://prove2.me/theorems/33346dd7-c97c-4cda-8395-a74c2e48a606
-- title:
--   Realized product tomography implies both spanning and fiducial minimality on the clump label set
-- statement:
--   For a qubit region with reconstruction, a realized table of independent product tests across clump starts implies both spanning of the physical preparation vectors and minimality of the proposed clump fiducial labels. The statement uses the actual decoded indices on each wire.
-- source:
--   Hardy, arXiv:0804.0054, section 5, interior tomography and fiducial minimality.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_product_tests_span
import Theorems.Thm_HardyFLocal_clump_coordinate_equivalence
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem clump_fiducial_from_test_table {m n : ℕ} (M : Model (Setting m n) (Outcome m n))
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (recovers : ∀ α s, regionTable M O α s = (actualCausaloid S L).r O α ⬝ᵥ (actualCausaloid S L).state M O s)
    {T : Type} [Fintype T] (w : Ω → T → ℝ) (hw : LinearIndependent ℝ w)
    (tests : ∀ t : {i : O × Bool // IsClumpStart O (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val} → T,
      ∃ s, ∀ k : omegaC L O, (actualCausaloid S L).state M O s k =
        ∏ i, w (if i.val.2 then (famPairs L O k.val i.val.1.val).1 else (famPairs L O k.val i.val.1.val).2) (t i)) :
    Submodule.span ℝ (Set.range ((actualCausaloid S L).state M O)) = ⊤ ∧
      Fiducial (regionTable M O) ((actualCausaloid S L).fidSet O) := by sorry

end HardyFLocal
