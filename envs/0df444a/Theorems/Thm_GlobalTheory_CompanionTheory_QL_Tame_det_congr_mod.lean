-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_congr_mod
-- name    : GlobalTheory.CompanionTheory.QL.Tame.det_congr_mod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:20.100718+00:00
-- url     : https://prove2.me/theorems/b79a7c88-81ff-4d52-b2bc-94197a1f84cc
-- title:
--   Tame: det congr mod
-- statement:
--   The Tame construction uses the det congr mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L29-L52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.Tame.det_congr_mod {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
    (X Y : Matrix ι ι F) (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O)
    (h : ∀ i j, ∃ o ∈ O, X i j - Y i j = ϖ * o) : ∃ o ∈ O, X.det - Y.det = ϖ * o := by sorry
