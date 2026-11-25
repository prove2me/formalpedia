-- Prove2me | Theorems.Thm_GlobalTheory_T_isSemisimple_of_locallyFinite_compactGroup
-- name    : GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:42.397172+00:00
-- url     : https://prove2.me/theorems/8e665a23-2e29-42f2-b049-7ec54190701b
-- title:
--   T: is Semisimple of locally Finite compact Group
-- statement:
--   The T construction uses the is Semisimple of locally Finite compact Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroupStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroupStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup : ∀ (K V : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) → ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by sorry
