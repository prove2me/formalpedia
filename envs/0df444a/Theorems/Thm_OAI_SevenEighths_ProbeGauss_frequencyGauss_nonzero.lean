-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGauss_frequencyGauss_nonzero
-- name    : OAI.SevenEighths.ProbeGauss.frequencyGauss_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:23.841505+00:00
-- url     : https://prove2.me/theorems/0e8a739d-7868-4d51-a4bc-b32cb0fcf1b5
-- title:
--   Probe Gauss: frequency Gauss nonzero
-- statement:
--   The Probe Gauss construction uses the frequency Gauss nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L20-L23
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L20-L23

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

theorem OAI.SevenEighths.ProbeGauss.frequencyGauss_nonzero {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by sorry
