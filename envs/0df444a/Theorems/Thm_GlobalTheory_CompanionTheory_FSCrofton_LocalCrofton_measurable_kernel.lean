-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_measurable_kernel
-- name    : GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.measurable_kernel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:08.575341+00:00
-- url     : https://prove2.me/theorems/010016fa-901f-4f99-951d-00126712243e
-- title:
--   Local Crofton: measurable kernel
-- statement:
--   The Local Crofton construction uses the measurable kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L83-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L83-L97

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton

theorem GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.measurable_kernel {X : Type} [MeasurableSpace X] (d : ℕ) (β : Type) [Fintype β]
    (g : β → X → ℂ) (F : β → Fin d → X → ℂ) (hg : ∀ j, Measurable (g j))
    (hF : ∀ j a, Measurable (F j a)) :
    Measurable fun p : (Fin d → β → ℂ) × X =>
      gW d β p.1 * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, p.1 k j * g j p.2‖ ^ 2) *
        ‖(Matrix.of p.1 * (Matrix.of fun j a => F j a p.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by sorry
