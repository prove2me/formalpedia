-- Prove2me | Theorems.Thm_GlobalTheory_Published_Metaplectic_Model_shear_coeff
-- name    : GlobalTheory.Published.Metaplectic.Model.shear_coeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:05.612174+00:00
-- url     : https://prove2.me/theorems/51febc0d-9eea-5de1-9e58-378b7304aeb0
-- title:
--   Model: shear coeff
-- statement:
--   The Model construction uses the shear coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HolPartShear.lean#L36-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HolPartShear.lean#L36-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.Published.Metaplectic.Model.shear_coeff (c : ℝ) :
    (∫ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 * ((2 + I * c) / 2) =
      (∫ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 := by sorry
