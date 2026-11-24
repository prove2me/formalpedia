-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_exists_entire_ne_zero
-- name    : GlobalTheory.HeckeOne.exists_entire_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:22.674885+00:00
-- url     : https://prove2.me/theorems/a3443186-38cf-448f-a1b0-c33c34caa239
-- title:
--   Hecke One: exists entire ne zero
-- statement:
--   The Hecke One construction uses the exists entire ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L142-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.HeckeOne.exists_entire_ne_zero (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) {χ : HChar K} (hu : χ.IsUnitary)
    (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) : ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ 1 ≠ 0 := by sorry
