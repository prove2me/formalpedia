-- Prove2me | Theorems.Thm_GlobalTheory_WittTrace_exists_dual_ne_zero
-- name    : GlobalTheory.WittTrace.exists_dual_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:18.191672+00:00
-- url     : https://prove2.me/theorems/3a7e5577-7638-4923-957d-1d51862efb16
-- title:
--   Witt Trace: exists dual ne zero
-- statement:
--   The Witt Trace construction uses the exists dual ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L12-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

theorem GlobalTheory.WittTrace.exists_dual_ne_zero (H : Submodule E V) {x y : V} (hx : x ∉ H) (hy : y ∉ H) :
    ∃ ψ : V →ₗ[E] E, (∀ h ∈ H, ψ h = 0) ∧ ψ x ≠ 0 ∧ ψ y ≠ 0 := by sorry
