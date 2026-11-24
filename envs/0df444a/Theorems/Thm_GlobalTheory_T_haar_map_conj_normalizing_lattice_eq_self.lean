-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_map_conj_normalizing_lattice_eq_self
-- name    : GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:41:56.72641+00:00
-- url     : https://prove2.me/theorems/8d7967ef-b4e5-44f4-8d52-21a5d013deab
-- title:
--   T: haar map conj normalizing lattice eq self
-- statement:
--   The T construction uses the haar map conj normalizing lattice eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapConjNormalizingLatticeEqSelfStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapConjNormalizingLatticeEqSelfStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) := by sorry
