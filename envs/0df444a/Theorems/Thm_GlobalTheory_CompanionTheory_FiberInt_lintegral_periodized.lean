-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_lintegral_periodized
-- name    : GlobalTheory.CompanionTheory.FiberInt.lintegral_periodized
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:11.354931+00:00
-- url     : https://prove2.me/theorems/656ebe42-dd4f-483d-b6a3-ba076fa42581
-- title:
--   Fiber Int: lintegral periodized
-- statement:
--   The Fiber Int construction uses the lintegral periodized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L17-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FiberInt
variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']

theorem GlobalTheory.CompanionTheory.FiberInt.lintegral_periodized {π : A →+ A'} (hπ : Measurable π) {Γ' : AddSubgroup A'} [Countable Γ']
    (lam : Measure A) (𝓖 : Set A) {f : A' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(periodized π Γ' lam 𝓖) = ∫⁻ x in 𝓖, ∑' γ : Γ', f ((γ : A') + π x) ∂lam := by sorry
