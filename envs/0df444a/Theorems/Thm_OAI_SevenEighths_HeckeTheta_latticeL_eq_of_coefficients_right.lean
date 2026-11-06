-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_eq_of_coefficients_right
-- name    : OAI.SevenEighths.HeckeTheta.latticeL_eq_of_coefficients_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:21.13603+00:00
-- url     : https://prove2.me/theorems/f6012317-1bae-4d60-877c-c82e334659e9
-- title:
--   Hecke Theta: lattice L eq of coefficients right
-- statement:
--   The Hecke Theta construction uses the lattice L eq of coefficients right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FamilySeries.lean#L11-L17
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FamilySeries.lean#L11-L17

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FamilySeries
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem OAI.SevenEighths.HeckeTheta.latticeL_eq_of_coefficients_right {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 1 < s.re) : latticeL w s = latticeL v s := by sorry
