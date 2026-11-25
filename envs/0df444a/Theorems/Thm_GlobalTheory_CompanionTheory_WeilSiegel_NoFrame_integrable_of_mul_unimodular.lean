-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_NoFrame_integrable_of_mul_unimodular
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.integrable_of_mul_unimodular
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:34.834732+00:00
-- url     : https://prove2.me/theorems/aa98949f-a5b3-5648-b4e6-fa7ce54a2b9c
-- title:
--   No Frame: integrable of mul unimodular
-- statement:
--   The No Frame construction uses the integrable of mul unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableOfMulUnimodular.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableOfMulUnimodular.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.integrable_of_mul_unimodular {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by sorry
