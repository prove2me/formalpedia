-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_marked_table_resummation
-- name    : OAI.SevenEighths.ProbeEuler.marked_table_resummation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:54.007446+00:00
-- url     : https://prove2.me/theorems/f215348f-c5ce-44f3-adc2-ad9b6b0236af
-- title:
--   Probe Euler: marked table resummation
-- statement:
--   The Probe Euler construction uses the marked table resummation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Euler.lean#L18-L34
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Euler.lean#L18-L34

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem OAI.SevenEighths.ProbeEuler.marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by sorry
