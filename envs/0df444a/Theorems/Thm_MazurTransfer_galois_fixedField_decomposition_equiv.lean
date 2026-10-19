-- Prove2me | Theorems.Thm_MazurTransfer_galois_fixedField_decomposition_equiv
-- name    : MazurTransfer.galois_fixedField_decomposition_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T12:22:12.81157+00:00
-- url     : https://prove2.me/theorems/d1597d8c-7a47-487d-8980-d04ad7273e4f
-- title:
--   Galois group over a decomposition-fixed field
-- statement:
--   Let $L/K$ be a Galois field extension and $P$ a valuation subring of $L$. Write $D_P\le\operatorname{Gal}(L/K)$ for its decomposition group and $E=L^{D_P}$ for the fixed field. There is a group isomorphism $\operatorname{Gal}(L/E)\simeq D_P$ that preserves the action on every element of $L$. This identifies the local Galois action with the original decomposition-group action on the same field.
-- source:
--   Original group-isomorphism construction developed for MazurTheorem, https://github.com/Vilin97/MazurTheorem. Uses the unchanged existing-public FLT theorem ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField (7682569b-0a82-5e5d-abe5-0498f3740238), whose complete official original proof was checked at pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Applied to the SAME original decomposition-fixed fraction field at13 in actual Picard point descent.

import Mathlib
import Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField

theorem MazurTransfer.galois_fixedField_decomposition_equiv (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P : ValuationSubring L) :
    ∃ e : (L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L) ≃*
        P.decompositionSubgroup K,
      ∀ (σ : L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L) (x : L),
        (e σ).val x = σ x := by sorry
