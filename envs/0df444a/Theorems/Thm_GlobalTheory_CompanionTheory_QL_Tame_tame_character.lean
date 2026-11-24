-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_tame_character
-- name    : GlobalTheory.CompanionTheory.QL.Tame.tame_character
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:48.880204+00:00
-- url     : https://prove2.me/theorems/7b4cb7bc-60be-40d8-a044-499e25c3faf7
-- title:
--   Tame: tame character
-- statement:
--   The Tame construction uses the tame character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L197-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricCharacterModulusProperties.lean#L197-L235

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

theorem GlobalTheory.CompanionTheory.QL.Tame.tame_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by sorry
