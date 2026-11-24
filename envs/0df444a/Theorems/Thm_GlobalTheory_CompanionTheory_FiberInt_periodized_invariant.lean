-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_periodized_invariant
-- name    : GlobalTheory.CompanionTheory.FiberInt.periodized_invariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:21.394662+00:00
-- url     : https://prove2.me/theorems/4e98d983-a198-4fcd-963b-a40e94b639e5
-- title:
--   Fiber Int: periodized invariant
-- statement:
--   The Fiber Int construction uses the periodized invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L28-L57

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

theorem GlobalTheory.CompanionTheory.FiberInt.periodized_invariant {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} [lam.IsAddHaarMeasure] {𝓖 : Set A}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) :
    (periodized π Γ' lam 𝓖).IsAddLeftInvariant := by sorry
