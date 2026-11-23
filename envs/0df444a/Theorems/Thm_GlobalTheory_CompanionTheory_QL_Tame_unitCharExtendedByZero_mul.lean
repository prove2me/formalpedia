-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_unitCharExtendedByZero_mul
-- name    : GlobalTheory.CompanionTheory.QL.Tame.unitCharExtendedByZero_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:59.182325+00:00
-- url     : https://prove2.me/theorems/7a1e5fdb-96b6-4470-8764-d47062a5ea6c
-- title:
--   Tame: unit Char Extended By Zero mul
-- statement:
--   The Tame construction uses the unit Char Extended By Zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L72-L76

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

theorem GlobalTheory.CompanionTheory.QL.Tame.unitCharExtendedByZero_mul (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by sorry
