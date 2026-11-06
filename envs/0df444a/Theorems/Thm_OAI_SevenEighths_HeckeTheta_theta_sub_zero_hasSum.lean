-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_theta_sub_zero_hasSum
-- name    : OAI.SevenEighths.HeckeTheta.theta_sub_zero_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:51.120652+00:00
-- url     : https://prove2.me/theorems/f4861f53-0b8b-4888-8445-7c3e237cf96c
-- title:
--   Hecke Theta: theta sub zero has Sum
-- statement:
--   The Hecke Theta construction uses the theta sub zero has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L26-L39
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L26-L39

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

theorem OAI.SevenEighths.HeckeTheta.theta_sub_zero_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by sorry
