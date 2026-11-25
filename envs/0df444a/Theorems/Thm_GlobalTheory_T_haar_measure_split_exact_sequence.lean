-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_measure_split_exact_sequence
-- name    : GlobalTheory.T.haar_measure_split_exact_sequence
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:17.752812+00:00
-- url     : https://prove2.me/theorems/1bfa8c65-9974-4e02-a6a6-8a383dc6ef0c
-- title:
--   T: haar measure split exact sequence
-- statement:
--   The T construction uses the haar measure split exact sequence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequenceStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequenceStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequenceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_measure_split_exact_sequence : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by sorry
