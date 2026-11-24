-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_comm_pow_of_apply
-- name    : GlobalTheory.SmoothForms.comm_pow_of_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:24.819805+00:00
-- url     : https://prove2.me/theorems/53fa6abd-c5cd-48dc-a286-831e0b99f41d
-- title:
--   Smooth Forms: comm pow of apply
-- statement:
--   The Smooth Forms construction uses the comm pow of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L44-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}

theorem GlobalTheory.SmoothForms.comm_pow_of_apply (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ)
    (c e : Fin n) : E a b * (Matrix.of E ^ m) c e - (Matrix.of E ^ m) c e * E a b =
      (if b = c then (Matrix.of E ^ m) a e else 0) - (if e = a then (Matrix.of E ^ m) c b else 0) := by sorry
