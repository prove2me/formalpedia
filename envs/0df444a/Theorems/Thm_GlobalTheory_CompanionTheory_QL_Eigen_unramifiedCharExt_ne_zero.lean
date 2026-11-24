-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_unramifiedCharExt_ne_zero
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.unramifiedCharExt_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:38.158795+00:00
-- url     : https://prove2.me/theorems/590a1d88-beb1-4f10-9be3-7e3765e024ad
-- title:
--   Eigen: unramified Char Ext ne zero
-- statement:
--   The Eigen construction uses the unramified Char Ext ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L24-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.Eigen.unramifiedCharExt_ne_zero (δ : Fˣ →* ℂˣ) {x : F} (hx : x ≠ 0) : chi0 δ x ≠ 0 := by sorry
