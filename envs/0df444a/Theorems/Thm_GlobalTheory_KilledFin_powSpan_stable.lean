-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_powSpan_stable
-- name    : GlobalTheory.KilledFin.powSpan_stable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:25.392161+00:00
-- url     : https://prove2.me/theorems/12b1e82c-a72f-4f5f-b538-1db281a58646
-- title:
--   Killed Fin: pow Span stable
-- statement:
--   The Killed Fin construction uses the pow Span stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L113-L125

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

theorem GlobalTheory.KilledFin.powSpan_stable (t u : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V)
    (hu : ∀ n ∈ N, u n ∈ N) (hc : Commute u t) (v : V) (hv : v ∈ powSpan t d N) :
    u v ∈ powSpan t d N := by sorry
