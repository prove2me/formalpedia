-- Prove2me | Theorems.Thm_NumberField_not_dvd_discr_sup_of_not_dvd_discr
-- name    : NumberField.not_dvd_discr_sup_of_not_dvd_discr
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T16:33:13.57264+00:00
-- url     : https://prove2.me/theorems/dc626c0e-c6c5-4336-86c7-d6d33593a758
-- title:
--   A compositum of two extensions unramified at a prime is unramified there
-- statement:
--   Let $K_1$ and $K_2$ be number fields inside a common algebraic closure of $\mathbf Q$. If a rational prime $\ell$ divides neither $\operatorname{disc}(K_1)$ nor $\operatorname{disc}(K_2)$, then it does not divide the discriminant of their compositum $K_1K_2$.
-- source:
--   Stability of finite etale algebras under tensor product and localization; equivalently, composita of local unramified extensions are unramified.

import Definitions.Def_MTT_Arithmetic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false
noncomputable section

/-- If a rational prime is unramified in two number fields embedded in a
common algebraic closure, then it is unramified in their compositum. -/
theorem NumberField.not_dvd_discr_sup_of_not_dvd_discr
    (K₁ K₂ : IntermediateField ℚ MTT.Qbar)
    [NumberField K₁] [NumberField K₂]
    {l : ℤ} (hl : Prime l)
    (h₁ : ¬ l ∣ NumberField.discr K₁)
    (h₂ : ¬ l ∣ NumberField.discr K₂) :
    letI : NumberField ↥(K₁ ⊔ K₂) :=
      { to_charZero := inferInstance
        to_finiteDimensional := IntermediateField.finiteDimensional_sup K₁ K₂ }
    ¬ l ∣ NumberField.discr ↥(K₁ ⊔ K₂) := by sorry
