-- Prove2me | Theorems.Thm_MazurTransfer_order18_normalized_cubic_unique_root
-- name    : MazurTransfer.order18_normalized_cubic_unique_root
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:37:56.937732+00:00
-- url     : https://prove2.me/theorems/7f0880d6-5f2f-4250-9822-cff8d32a5583
-- title:
--   The normalized order-18 cubic has exactly one dyadic coefficient root
-- statement:
--   In $C=(\mathbb Z/16\mathbb Z)^3$ with the fixed cubic multiplication, the normalized relative cubic has exactly one root: $$z^3+(\tau^2-3)z^2+(-2\tau^2+\tau+4)z-1=0\quad\Longleftrightarrow\quad z=(7,10,1).$$ This is the complete enumeration of all $16^3$ coefficient triples. The downstream order-18 descent separately proves that the relevant integral element reduces into this ring and satisfies this polynomial; this theorem supplies exactly its unique residue vector.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XOneEighteenDyadicGeneratorRingCertificate.lean, normalizedRelativeCubicValue_eq_zero_iff. Original three-coordinate kernel enumeration retained, with no numerical oracle.

import Mathlib
import Definitions.Def_MazurTransfer_OrderEighteenNormalizedCubicData

theorem MazurTransfer.order18_normalized_cubic_unique_root :
    ∀ z : Fin 3 → ZMod 16,
      MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate.normalizedRelativeCubicValue z = 0 ↔
        z = MazurTorsion.XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by sorry
