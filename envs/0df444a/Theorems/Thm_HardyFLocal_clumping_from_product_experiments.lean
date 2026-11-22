-- Prove2me | Theorems.Thm_HardyFLocal_clumping_from_product_experiments
-- name    : HardyFLocal.clumping_from_product_experiments
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:09:54.096888+00:00
-- url     : https://prove2.me/theorems/f91a0269-14bb-4882-823f-213c52bc41f4
-- title:
--   It suffices to prove the clumping identity on fully product experiments
-- statement:
--   To reconstruct probabilities for all operations inside and outside a finite qubit region, it suffices to prove the clump identity when every operation in the experiment is a fiducial product. The initial state can be arbitrary and the exterior may contain entangling operations.
-- source:
--   Hardy, arXiv:0804.0054, section 5. Reduction of all-region clumping to product experiments.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_grid_region_expansion
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem clumping_from_product_experiments {m n : ℕ} (ρ : GlobalMat m n)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M)
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (productExperiment : ∀ (l : ∀ x : O, omegaOne L x.val) (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      (∀ x, x ∉ O → s x ∈ omegaOne L x) →
      regionTable M O (fun x => (l x).val) s =
        ∑ k : omegaC L O, (actualCausaloid S L).Λ O l k * (actualCausaloid S L).state M O s k) :
    ∀ (α : Lab (Setting m n) (Outcome m n) O) (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      regionTable M O α s = (actualCausaloid S L).r O α ⬝ᵥ (actualCausaloid S L).state M O s := by sorry

end HardyFLocal
