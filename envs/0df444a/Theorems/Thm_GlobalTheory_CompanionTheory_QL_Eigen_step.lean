-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_step
-- name    : GlobalTheory.CompanionTheory.QL.Eigen.step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:32.115891+00:00
-- url     : https://prove2.me/theorems/db750655-3065-48f9-8736-4230e312ccd1
-- title:
--   Eigen: step
-- statement:
--   The Eigen construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L145-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean#L145-L184

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

theorem GlobalTheory.CompanionTheory.QL.Eigen.step (hLF : LF O ϖ nrm q) (δ : Fˣ →* ℂˣ) (hδ : Del nrm δ) {r d c : ℕ}
    {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) {x : Matrix (Fin (r + d)) (Fin (r + c)) F}
    (hx : Supp O ϖ x) :
    Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∧
      chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det =
        chi0 δ (bAA x).det * chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det := by sorry
