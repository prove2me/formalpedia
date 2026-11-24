-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_span_adjoin_apply_stable
-- name    : GlobalTheory.KilledFin.span_adjoin_apply_stable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:46.868886+00:00
-- url     : https://prove2.me/theorems/fc60b642-4a8b-4f02-b2cd-2fd89b517e29
-- title:
--   Killed Fin: span adjoin apply stable
-- statement:
--   The Killed Fin construction uses the span adjoin apply stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L33-L46

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

theorem GlobalTheory.KilledFin.span_adjoin_apply_stable (s : Set (Module.End ℂ V)) (ψ : V) (u : Module.End ℂ V)
    (hu : u ∈ Algebra.adjoin ℂ s) (v : V)
    (hv : v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))) :
    u v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V))) := by sorry
