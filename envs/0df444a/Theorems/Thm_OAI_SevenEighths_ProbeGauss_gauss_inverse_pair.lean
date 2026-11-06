-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGauss_gauss_inverse_pair
-- name    : OAI.SevenEighths.ProbeGauss.gauss_inverse_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:47.496887+00:00
-- url     : https://prove2.me/theorems/893848bd-dc09-474a-92a9-2a5cc6c83c71
-- title:
--   Probe Gauss: gauss inverse pair
-- statement:
--   The Probe Gauss construction uses the gauss inverse pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L50-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L50-L54

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

theorem OAI.SevenEighths.ProbeGauss.gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by sorry
