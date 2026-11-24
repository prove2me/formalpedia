-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Diag_exists_eq_transpose_mul_self
-- name    : GlobalTheory.CompanionTheory.SW.Diag.exists_eq_transpose_mul_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:38.694251+00:00
-- url     : https://prove2.me/theorems/c18fa8a7-f04d-4148-90da-6ec82dd9e559
-- title:
--   Diag: exists eq transpose mul self
-- statement:
--   The Diag construction uses the exists eq transpose mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SimultaneousNormalFormMajorant.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SimultaneousNormalFormMajorant.lean#L9-L28

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Diag
open scoped MatrixOrder

theorem GlobalTheory.CompanionTheory.SW.Diag.exists_eq_transpose_mul_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℝ} (hT : T.PosSemidef) : ∃ B : Matrix ι ι ℝ, T = Bᵀ * B := by sorry
