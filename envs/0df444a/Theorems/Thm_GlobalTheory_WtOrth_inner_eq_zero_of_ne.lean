-- Prove2me | Theorems.Thm_GlobalTheory_WtOrth_inner_eq_zero_of_ne
-- name    : GlobalTheory.WtOrth.inner_eq_zero_of_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:46.635811+00:00
-- url     : https://prove2.me/theorems/f8129228-41fa-4e5a-93a8-7ff9a128c13a
-- title:
--   Wt Orth: inner eq zero of ne
-- statement:
--   The Wt Orth construction uses the inner eq zero of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecomp.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecomp.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.WtOrth

theorem GlobalTheory.WtOrth.inner_eq_zero_of_ne {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by sorry
