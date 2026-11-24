-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_comm_sub_const
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.comm_sub_const
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:38.152795+00:00
-- url     : https://prove2.me/theorems/2a97852e-c7bf-49c5-a9fc-e55b4a5380a8
-- title:
--   Schur Char: comm sub const
-- statement:
--   The Schur Char construction uses the comm sub const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L39-L47

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

theorem GlobalTheory.CompanionTheory.SW.SchurChar.comm_sub_const {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    {f : V → ℂ} (h : Comm T f) (c : ℂ) : Comm T (fun u => f u - c) := by sorry
