-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_char_locConst
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.char_locConst
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:25.274794+00:00
-- url     : https://prove2.me/theorems/8e68bd18-d6a3-4479-bc17-4b4554a289f4
-- title:
--   Schur Char: char loc Const
-- statement:
--   The Schur Char construction uses the char loc Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L62-L75

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}

theorem GlobalTheory.CompanionTheory.SW.SchurChar.char_locConst (h : NADual V χ μ) (y : V) : IsLocallyConstant (fun u => χ u y) := by sorry
