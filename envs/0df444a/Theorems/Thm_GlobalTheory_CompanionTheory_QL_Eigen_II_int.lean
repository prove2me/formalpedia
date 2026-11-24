-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_II_int
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.II_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:50.873161+00:00
-- url     : https://prove2.me/theorems/0fef2ec4-a78b-4618-8c88-857b4a79dedf
-- title:
--   Eigen: II int
-- statement:
--   The Eigen construction uses the II int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L76-L79

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

theorem GlobalTheory.CompanionTheory.QL.Eigen.II_int {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {a b : ℕ} {X : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) : X ∈ intMat O a b := by sorry
