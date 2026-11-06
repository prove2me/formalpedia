-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGauss_frequencyGauss_principal
-- name    : OAI.SevenEighths.ProbeGauss.frequencyGauss_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:40:39.433851+00:00
-- url     : https://prove2.me/theorems/61f646ae-4858-463b-8637-4ec95bc2c968
-- title:
--   Probe Gauss: frequency Gauss principal
-- statement:
--   The Probe Gauss construction uses the frequency Gauss principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L38-L48
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L38-L48

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

theorem OAI.SevenEighths.ProbeGauss.frequencyGauss_principal {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (h : F) :
    frequencyGauss 1 ψ h = if h = 0 then (Nat.card Fˣ : ℂ) else -1 := by sorry
