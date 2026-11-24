-- Prove2me | Theorems.Thm_GlobalTheory_KilledFin_powSpan_finite
-- name    : GlobalTheory.KilledFin.powSpan_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:18.141204+00:00
-- url     : https://prove2.me/theorems/7e54d19e-5ea7-4d5e-9578-844021cf3765
-- title:
--   Killed Fin: pow Span finite
-- statement:
--   The Killed Fin construction uses the pow Span finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L140-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L140-L159

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

theorem GlobalTheory.KilledFin.powSpan_finite (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (powSpan t d N) ∧
      Module.finrank ℂ (powSpan t d N) ≤ d * Module.finrank ℂ N := by sorry
