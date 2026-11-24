-- Prove2me | Theorems.Thm_GlobalTheory_LocFinSemisimple_isSemisimple_ofInvariant
-- name    : GlobalTheory.LocFinSemisimple.isSemisimple_ofInvariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:23.705424+00:00
-- url     : https://prove2.me/theorems/e1bc0223-7ca5-48a4-99a6-7ccc0b9b1ccc
-- title:
--   Loc Fin Semisimple: is Semisimple of Invariant
-- statement:
--   The Loc Fin Semisimple construction uses the is Semisimple of Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L34-L44

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

theorem GlobalTheory.LocFinSemisimple.isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by sorry
