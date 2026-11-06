-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_completed_hasSum
-- name    : OAI.SevenEighths.HeckeTheta.completed_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:59.549961+00:00
-- url     : https://prove2.me/theorems/033b59b1-4123-4491-8331-8638c366da0f
-- title:
--   Hecke Theta: completed has Sum
-- statement:
--   The Hecke Theta construction uses the completed has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L41-L53
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L41-L53

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

theorem OAI.SevenEighths.HeckeTheta.completed_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by sorry
