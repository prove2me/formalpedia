-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_powSpan_stable_self
-- name    : GlobalTheory.KilledFin.powSpan_stable_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:15.42781+00:00
-- url     : https://prove2.me/theorems/ae0e4b9e-7cf4-4f0e-b04f-44b1a9303860
-- title:
--   Killed Fin: pow Span stable self
-- statement:
--   The Killed Fin construction uses the pow Span stable self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L96-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L96-L111

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

theorem GlobalTheory.KilledFin.powSpan_stable_self (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (v : V) (hv : v ∈ powSpan t q.natDegree N) :
    t v ∈ powSpan t q.natDegree N := by sorry
