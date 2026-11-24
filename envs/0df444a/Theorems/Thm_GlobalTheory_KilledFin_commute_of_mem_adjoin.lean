-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_commute_of_mem_adjoin
-- name    : GlobalTheory.KilledFin.commute_of_mem_adjoin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:16.523891+00:00
-- url     : https://prove2.me/theorems/a88a2eca-fc8f-4648-a6a6-14480ef81466
-- title:
--   Killed Fin: commute of mem adjoin
-- statement:
--   The Killed Fin construction uses the commute of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L48-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L48-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.KilledFin.commute_of_mem_adjoin (s : Set (Module.End ℂ V)) (t : Module.End ℂ V)
    (ht : ∀ u ∈ s, Commute u t) (z : Module.End ℂ V) (hz : z ∈ Algebra.adjoin ℂ s) (q : ℂ[X]) :
    Commute z (aeval t q) := by sorry
