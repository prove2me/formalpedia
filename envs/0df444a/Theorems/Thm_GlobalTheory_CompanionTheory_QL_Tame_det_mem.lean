-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_mem
-- name    : GlobalTheory.CompanionTheory.QL.Tame.det_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:15.478628+00:00
-- url     : https://prove2.me/theorems/617c3ed0-ce78-40ed-a457-61f7f60fb333
-- title:
--   Tame: det mem
-- statement:
--   The Tame construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L25-L27

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

theorem GlobalTheory.CompanionTheory.QL.Tame.det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) : X.det ∈ O := by sorry
