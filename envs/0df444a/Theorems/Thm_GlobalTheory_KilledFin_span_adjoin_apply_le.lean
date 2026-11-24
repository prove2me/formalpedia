-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_span_adjoin_apply_le
-- name    : GlobalTheory.KilledFin.span_adjoin_apply_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:43.59405+00:00
-- url     : https://prove2.me/theorems/9e3b899d-2640-4fc0-b391-72e903e544fa
-- title:
--   Killed Fin: span adjoin apply le
-- statement:
--   The Killed Fin construction uses the span adjoin apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L9-L31

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

theorem GlobalTheory.KilledFin.span_adjoin_apply_le (s : Set (Module.End ℂ V)) (K : Submodule ℂ V)
    (hs : ∀ u ∈ s, ∀ v ∈ K, u v ∈ K) (ψ : V) (hψ : ψ ∈ K) :
    Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))
      ≤ K := by sorry
