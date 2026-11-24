-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_mul
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.sb_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:44.502361+00:00
-- url     : https://prove2.me/theorems/4f0c97ce-2cf2-4f71-984a-80ec75dcd14f
-- title:
--   Schur Char: sb mul
-- statement:
--   The Schur Char construction uses the sb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L18-L20

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

theorem GlobalTheory.CompanionTheory.SW.SchurChar.sb_mul {m φ : V → ℂ} (hm : IsLocallyConstant m) (h : SB φ) :
    SB (fun u => m u * φ u) := by sorry
