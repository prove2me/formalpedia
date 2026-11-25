-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_intMat_mul
-- name    : GlobalTheory.CompanionTheory.QLScale.intMat_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:41.68056+00:00
-- url     : https://prove2.me/theorems/6c3fdb97-552c-4c99-b659-15dad01258eb
-- title:
--   QLScale: int Mat mul
-- statement:
--   The QLScale construction uses the int Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L52-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QLScale.intMat_mul {n m : ℕ} {x : Matrix (Fin n) (Fin m) F} {g : Matrix (Fin m) (Fin m) F}
    (hx : x ∈ intMat O n m) (hg : IsInt O g) : x * g ∈ intMat O n m := by sorry
