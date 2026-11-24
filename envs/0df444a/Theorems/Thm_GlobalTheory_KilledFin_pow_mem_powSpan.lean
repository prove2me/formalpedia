-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_pow_mem_powSpan
-- name    : GlobalTheory.KilledFin.pow_mem_powSpan
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:51.523797+00:00
-- url     : https://prove2.me/theorems/e3c69a65-6ba7-451c-8554-b4e8b7fca384
-- title:
--   Killed Fin: pow mem pow Span
-- statement:
--   The Killed Fin construction uses the pow mem pow Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L78-L94

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

theorem GlobalTheory.KilledFin.pow_mem_powSpan (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (n : V) (hn : n ∈ N) :
    (t ^ q.natDegree) n ∈ powSpan t q.natDegree N := by sorry
