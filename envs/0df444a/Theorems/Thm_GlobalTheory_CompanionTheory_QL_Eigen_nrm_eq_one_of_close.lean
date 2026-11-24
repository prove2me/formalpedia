-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_nrm_eq_one_of_close
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.nrm_eq_one_of_close
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:18.889894+00:00
-- url     : https://prove2.me/theorems/ba134dda-f3fe-4fed-a097-60af596191b2
-- title:
--   Eigen: nrm eq one of close
-- statement:
--   The Eigen construction uses the nrm eq one of close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L111-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L111-L122

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

theorem GlobalTheory.CompanionTheory.QL.Eigen.nrm_eq_one_of_close {nrm : AbsoluteValue F ℝ}
    (hna : ∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) {u v : F} (hv : nrm v = 1)
    (h : nrm (u - v) < 1) : nrm u = 1 := by sorry
