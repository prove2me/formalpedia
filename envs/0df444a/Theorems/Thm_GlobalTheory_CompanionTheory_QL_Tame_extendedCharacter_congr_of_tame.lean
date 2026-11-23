-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_congr_of_tame
-- name    : GlobalTheory.CompanionTheory.QL.Tame.extendedCharacter_congr_of_tame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:37.137422+00:00
-- url     : https://prove2.me/theorems/62836da0-84f1-4770-b6e5-ab64f9a78876
-- title:
--   Tame: extended Character congr of tame
-- statement:
--   The Tame construction uses the extended Character congr of tame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L78-L96

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

theorem GlobalTheory.CompanionTheory.QL.Tame.extendedCharacter_congr_of_tame {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {x y : F}
    (hy : nrm y = 1) (hxy : nrm (x - y) < 1) : chi0 δ x = chi0 δ y := by sorry
