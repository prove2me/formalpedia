-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_emb_dotProduct_DM
-- name    : GlobalTheory.CompanionTheory.SW.ThW.emb_dotProduct_DM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:11:08.456783+00:00
-- url     : https://prove2.me/theorems/45ee4c35-18ce-4c5e-9faa-78ca524d808e
-- title:
--   Th W: emb dot Product DM
-- statement:
--   The Th W construction uses the emb dot Product DM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L25-L34

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

theorem GlobalTheory.CompanionTheory.SW.ThW.emb_dotProduct_DM {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by sorry
