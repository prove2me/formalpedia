-- Prove2me | Theorems.Thm_OAI_FourierBridge_logPhase_continuous_left
-- name    : OAI.FourierBridge.logPhase_continuous_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:48.120483+00:00
-- url     : https://prove2.me/theorems/6b216adc-29a1-455b-b043-420576448306
-- title:
--   Fourier Bridge: log Phase continuous left
-- statement:
--   The Fourier Bridge construction uses the log Phase continuous left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L186-L189
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L186-L189

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.FourierBridge
open scoped FourierTransform SchwartzMap

theorem OAI.FourierBridge.logPhase_continuous_left (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by sorry
