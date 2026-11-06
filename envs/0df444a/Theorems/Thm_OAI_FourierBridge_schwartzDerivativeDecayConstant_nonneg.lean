-- Prove2me | Theorems.Thm_OAI_FourierBridge_schwartzDerivativeDecayConstant_nonneg
-- name    : OAI.FourierBridge.schwartzDerivativeDecayConstant_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:09.992647+00:00
-- url     : https://prove2.me/theorems/dac1a396-31a6-49b5-80ff-9d98a6c21717
-- title:
--   Fourier Bridge: schwartz Derivative Decay Constant nonneg
-- statement:
--   The Fourier Bridge construction uses the schwartz Derivative Decay Constant nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1315-L1319
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1315-L1319

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge

theorem OAI.FourierBridge.schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by sorry
