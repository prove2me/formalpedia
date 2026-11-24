-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_measure_preimage_inter_eq
-- name    : GlobalTheory.CompanionTheory.FiberInt.measure_preimage_inter_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:24.595125+00:00
-- url     : https://prove2.me/theorems/bf54ff67-db07-4a2a-8520-c612d4ae0dec
-- title:
--   Fiber Int: measure preimage inter eq
-- statement:
--   The Fiber Int construction uses the measure preimage inter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L63-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean#L63-L127

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

theorem GlobalTheory.CompanionTheory.FiberInt.measure_preimage_inter_eq {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} {lam' : Measure A'} [lam.IsAddHaarMeasure]
    [lam'.IsAddHaarMeasure] {𝓖 : Set A} {𝓖' : Set A'}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (hG' : IsAddFundamentalDomain Γ' 𝓖' lam') (h1' : lam' 𝓖' = 1)
    {S : Set A'} (hS : MeasurableSet S) (hinv : ∀ γ ∈ Γ', ∀ x, γ + x ∈ S ↔ x ∈ S) :
    lam (π ⁻¹' S ∩ 𝓖) = lam' (S ∩ 𝓖') := by sorry
