-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_extendedCharacter_congr_of_tame
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.extendedCharacter_congr_of_tame
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:57.026835+00:00
-- url     : https://prove2.me/theorems/640e5af1-a859-4bdd-ac84-f2506cad981d
-- title:
--   Eigen: extended Character congr of tame
-- statement:
--   The Eigen construction uses the extended Character congr of tame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L28-L43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_congr_of_tame

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

theorem GlobalTheory.CompanionTheory.QL.Eigen.extendedCharacter_congr_of_tame (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ)
    (tame : ∀ x : Fˣ, nrm ((x : F) - 1) < 1 → δ x = 1) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : nrm (u - v) < nrm v) : chi0 δ u = chi0 δ v := by sorry
