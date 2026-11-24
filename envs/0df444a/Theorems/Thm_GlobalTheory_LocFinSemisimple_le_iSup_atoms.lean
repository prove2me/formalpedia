-- Prove2me | Theorems.Thm_GlobalTheory_LocFinSemisimple_le_iSup_atoms
-- name    : GlobalTheory.LocFinSemisimple.le_iSup_atoms
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:14.613103+00:00
-- url     : https://prove2.me/theorems/8b3aaa44-73a1-46c5-bde9-6fe294820a11
-- title:
--   Loc Fin Semisimple: le i Sup atoms
-- statement:
--   The Loc Fin Semisimple construction uses the le i Sup atoms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L46-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L46-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocFinSemisimple
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem GlobalTheory.LocFinSemisimple.le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by sorry
