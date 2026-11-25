-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_phiQ_eigen
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.phiQ_eigen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:44.097289+00:00
-- url     : https://prove2.me/theorems/7ffe45e0-93ff-5c2b-abca-b966cb02353b
-- title:
--   Eigen: phi Q eigen
-- statement:
--   The Eigen construction uses the phi Q eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L186-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L186-L223

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.Eigen.phiQ_eigen : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r d c : ℕ, ∀ k ∈ parJ O ϖ r c,
    ∀ x : Matrix (Fin (r + d)) (Fin (r + c)) F,
    ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) =
      lamJ δ k * phiQ O ϖ δ r d c x := by sorry
