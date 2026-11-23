-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_units
-- name    : GlobalTheory.CompanionTheory.QL.Tame.extendedCharacter_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:37.782704+00:00
-- url     : https://prove2.me/theorems/5d861080-17ce-497d-8450-575f67dc9764
-- title:
--   Tame: extended Character units
-- statement:
--   The Tame construction uses the extended Character units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L67-L70

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

theorem GlobalTheory.CompanionTheory.QL.Tame.extendedCharacter_units (δ : Fˣ →* ℂˣ) (u : Fˣ) : chi0 δ (u : F) = ((δ u : ℂˣ) : ℂ) := by sorry
