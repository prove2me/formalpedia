-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Vol_vol_IIset
-- name    : GlobalTheory.CompanionTheory.QL.Vol.vol_IIset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:28.982952+00:00
-- url     : https://prove2.me/theorems/cdec4c94-dba3-524c-967c-50015c1022f0
-- title:
--   Vol: vol IIset
-- statement:
--   The Vol construction uses the vol IIset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L31-L43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatrices
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Vol

theorem GlobalTheory.CompanionTheory.QL.Vol.vol_IIset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) = ENNReal.ofReal ((q : ℝ) ^ (-((n * m : ℕ) : ℤ))) := by sorry
