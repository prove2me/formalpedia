-- Prove2me | Theorems.Thm_OAI_SevenEighths_PeriodicThetaRegularity_theta_locallyIntegrable
-- name    : OAI.SevenEighths.PeriodicThetaRegularity.theta_locallyIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:52:59.005055+00:00
-- url     : https://prove2.me/theorems/bf69bf2b-3d32-4c98-9929-b1b42e12dbe9
-- title:
--   Periodic Theta Regularity: theta locally Integrable
-- statement:
--   The Periodic Theta Regularity construction uses the theta locally Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PeriodicThetaRegularity.lean#L34-L36
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PeriodicThetaRegularity.lean#L34-L36

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_PeriodicThetaRegularity
set_option autoImplicit false
open OAI
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta

theorem OAI.SevenEighths.PeriodicThetaRegularity.theta_locallyIntegrable {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    LocallyIntegrableOn (theta w) (Ioi 0) := by sorry
