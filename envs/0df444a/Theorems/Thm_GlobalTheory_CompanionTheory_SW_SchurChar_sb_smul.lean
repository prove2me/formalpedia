-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_smul
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.sb_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:03.620947+00:00
-- url     : https://prove2.me/theorems/17a20746-2f37-479d-b80e-f56af975664b
-- title:
--   Schur Char: sb smul
-- statement:
--   The Schur Char construction uses the sb smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L22-L23

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
variable {V : Type} [TopologicalSpace V]

theorem GlobalTheory.CompanionTheory.SW.SchurChar.sb_smul (c : ℂ) {φ : V → ℂ} (h : SB φ) : SB (c • φ) := by sorry
