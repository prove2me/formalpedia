-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_hasSum
-- name    : OAI.SevenEighths.HeckeTheta.latticeL_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:13.509513+00:00
-- url     : https://prove2.me/theorems/7af49add-d94f-421e-9e43-bfd4113dd23a
-- title:
--   Hecke Theta: lattice L has Sum
-- statement:
--   The Hecke Theta construction uses the lattice L has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L55-L67
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean#L55-L67

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

theorem OAI.SevenEighths.HeckeTheta.latticeL_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by sorry
