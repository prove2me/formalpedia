-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_not_isNormPow_of_not_unrAt
-- name    : GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:04:15.532831+00:00
-- url     : https://prove2.me/theorems/281c2aaf-90be-4e94-9eaa-e83c028c2e24
-- title:
--   Hecke One: not is Norm Pow of not unr At
-- statement:
--   The Hecke One construction uses the not is Norm Pow of not unr At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L101-L102

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

theorem GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : ¬ χ.UnrAt v) :
    ¬ ∃ t : ℝ, IsNormPow χ t := by sorry
