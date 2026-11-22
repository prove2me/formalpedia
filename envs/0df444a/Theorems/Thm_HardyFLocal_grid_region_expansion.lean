-- Prove2me | Theorems.Thm_HardyFLocal_grid_region_expansion
-- name    : HardyFLocal.grid_region_expansion
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:57:41.056052+00:00
-- url     : https://prove2.me/theorems/57d9ac0e-e71e-4fd2-b925-6a0ff36f7618
-- title:
--   Reconstruction of arbitrary qubit-region probabilities on the full fiducial grid
-- statement:
--   For all finite regions and arbitrary exterior preparations, the interacting-qubit model probability is reconstructed by expanding every regional vertex into its individual fiducial product labels with the elementary coordinates. This includes entangling operations both inside and outside the region.
-- source:
--   Hardy, arXiv:0804.0054, section 5, expansion (20) and clumping construction.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
import Theorems.Thm_HardyCausaloid_product_reconstruction
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem grid_region_expansion {m n : ℕ} (ρ : GlobalMat m n)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M)
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (α : Lab (Setting m n) (Outcome m n) O) (s : ∀ x, Label (Setting m n) (Outcome m n) x) :
    regionTable M O α s = ∑ l : ∀ x : O, omegaOne L x.val,
      (∏ x : O, elemCoeff S (labelOp (α x)) (decode L x.val (l x).val)) *
        regionTable M O (fun x => (l x).val) s := by sorry

end HardyFLocal
