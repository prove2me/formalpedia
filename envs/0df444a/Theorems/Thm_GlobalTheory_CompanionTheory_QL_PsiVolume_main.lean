-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_main
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:58.976794+00:00
-- url     : https://prove2.me/theorems/52f07f75-bef7-55c0-b9e0-454365a0e6fd
-- title:
--   Psi Volume: main
-- statement:
--   The Psi Volume construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L146-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L146-L161

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (δ η : Fˣ →* ℂˣ), Del nrm δ → Nu nrm η → ∀ r d c : ℕ, ∀ (dx : Measure (Matrix (Fin (r + d)) (Fin (r + c)) F)), dx.IsAddLeftInvariant → dx (intMat O (r + d) (r + c)) = 1 → ∀ (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F), MeasurableSet {x : Matrix (Fin (r + d)) (Fin (r + c)) F | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧ bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧ bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c} ∧ weilIP dx (omegaS (η * δ) nrm (pEl 1 B m) (phiQ O ϖ δ r d c)) (phiQ O ϖ δ r d c) = (((η * δ) (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) * ((nrm (m : Matrix (Fin c) (Fin c) F).det ^ (((r + d : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((dx {x : Matrix (Fin (r + d)) (Fin (r + c)) F | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧ bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧ bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c}).toReal : ℝ) : ℂ) := by sorry
