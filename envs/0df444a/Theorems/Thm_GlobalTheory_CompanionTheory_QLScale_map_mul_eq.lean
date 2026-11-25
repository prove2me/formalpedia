-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_map_mul_eq
-- name    : GlobalTheory.CompanionTheory.QLScale.map_mul_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:02.665412+00:00
-- url     : https://prove2.me/theorems/d994cd3b-da53-4925-b6f6-b750572f80f1
-- title:
--   QLScale: map mul eq
-- statement:
--   The QLScale construction uses the map mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L357-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L357-L393

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
variable [MeasurableSpace F] [BorelSpace F]

theorem GlobalTheory.CompanionTheory.QLScale.map_mul_eq (hLF : LF O ϖ nrm q) (n m : ℕ) (dx : Measure (Matrix (Fin n) (Fin m) F))
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) :
    (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F =>
        x * (g : Matrix (Fin m) (Fin m) F)) dx =
      ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧
    (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F =>
        (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) := by sorry
