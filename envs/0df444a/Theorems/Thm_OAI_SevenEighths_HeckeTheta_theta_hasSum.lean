-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_theta_hasSum
-- name    : OAI.SevenEighths.HeckeTheta.theta_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:25.750694+00:00
-- url     : https://prove2.me/theorems/196c1387-3a30-4ad3-83ce-2ee4a0dbf284
-- title:
--   Hecke Theta: theta has Sum
-- statement:
--   The Hecke Theta construction uses the theta has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L76-L110
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L76-L110

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem OAI.SevenEighths.HeckeTheta.theta_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by sorry
