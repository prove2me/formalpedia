-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_comm_mul
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.comm_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:13.613795+00:00
-- url     : https://prove2.me/theorems/62b2c821-f42c-4be3-938c-899637462778
-- title:
--   Schur Char: comm mul
-- statement:
--   The Schur Char construction uses the comm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L31-L37

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

theorem GlobalTheory.CompanionTheory.SW.SchurChar.comm_mul {T : (V → ℂ) → (V → ℂ)} {m m' : V → ℂ} (h : Comm T m) (h' : Comm T m') :
    Comm T (fun u => m u * m' u) := by sorry
