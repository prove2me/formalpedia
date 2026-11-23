-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_ZM_eq_blockDiagonal
-- name    : GlobalTheory.CompanionTheory.SW.ThW.ZM_eq_blockDiagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:51.103531+00:00
-- url     : https://prove2.me/theorems/0b5aba97-8dc4-4610-9850-e5b35b2b42c0
-- title:
--   Th W: ZM eq block Diagonal
-- statement:
--   The Th W construction uses the ZM eq block Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SiegelMatrixSymmetricPosdefImag.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SiegelMatrixSymmetricPosdefImag.lean#L41-L44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW

theorem GlobalTheory.CompanionTheory.SW.ThW.ZM_eq_blockDiagonal {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := by sorry
