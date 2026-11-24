-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_lam_mul
-- name    : GlobalTheory.CompanionTheory.QL.Tame.lam_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:51.869815+00:00
-- url     : https://prove2.me/theorems/54908eb8-d9cf-4bcc-9271-2ff0fda232f9
-- title:
--   Tame: lam mul
-- statement:
--   The Tame construction uses the lam mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L149-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L149-L193

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

theorem GlobalTheory.CompanionTheory.QL.Tame.lam_mul (h : LF O ϖ nrm q) {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {r c : ℕ}
    {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) :
    lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by sorry
