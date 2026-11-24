-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TestFunctionFibreIntegral_eventually_slice_eq
-- name    : GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.eventually_slice_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:31.821114+00:00
-- url     : https://prove2.me/theorems/bb09aa0c-4209-421d-a337-8cb2a3a3e168
-- title:
--   Test Function Fibre Integral: eventually slice eq
-- statement:
--   The Test Function Fibre Integral construction uses the eventually slice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PartialIntegralMemSchwartzBruhat.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PartialIntegralMemSchwartzBruhat.lean#L8-L30

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

theorem GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.eventually_slice_eq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by sorry
