-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_swapCurry_measurePreserving
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.swapCurry_measurePreserving
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:11:05.587551+00:00
-- url     : https://prove2.me/theorems/2f25745f-c3a0-4f6b-8f42-b28718287a8c
-- title:
--   Gauss Flat: swap Curry measure Preserving
-- statement:
--   The Gauss Flat construction uses the swap Curry measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L23-L39

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussFlat

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.swapCurry_measurePreserving (α β : Type) [Fintype α] [Fintype β] :
    MeasurePreserving (swapCurry α β) volume volume := by sorry
