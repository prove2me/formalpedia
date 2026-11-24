-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_par_data
-- name    : GlobalTheory.CompanionTheory.QL.Tame.par_data
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:38.91151+00:00
-- url     : https://prove2.me/theorems/038ffedc-5fda-421c-9cd5-9781be996b64
-- title:
--   Tame: par data
-- statement:
--   The Tame construction uses the par data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L105-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L105-L147

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.Tame.par_data (h : LF O ϖ nrm q) {r c : ℕ} {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    ∃ o ∈ O, (k : Matrix (Fin (r + c)) (Fin (r + c)) F).det -
      (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det *
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = ϖ * o := by sorry
