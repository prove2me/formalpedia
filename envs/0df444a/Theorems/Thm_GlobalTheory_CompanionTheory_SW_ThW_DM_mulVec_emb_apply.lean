-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DM_mulVec_emb_apply
-- name    : GlobalTheory.CompanionTheory.SW.ThW.DM_mulVec_emb_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:11:42.334328+00:00
-- url     : https://prove2.me/theorems/5ff7d9f2-4c87-41bb-9081-da1865620493
-- title:
--   Th W: DM mul Vec emb apply
-- statement:
--   The Th W construction uses the DM mul Vec emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L11-L23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem GlobalTheory.CompanionTheory.SW.ThW.DM_mulVec_emb_apply {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by sorry
