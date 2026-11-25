-- Prove2me | Theorems.Thm_GlobalTheory_DualFrames_hform_eq_dot
-- name    : GlobalTheory.DualFrames.hform_eq_dot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:37.059865+00:00
-- url     : https://prove2.me/theorems/3a1451bf-c226-5b9d-adde-6c10974b85ff
-- title:
--   Dual Frames: hform eq dot
-- statement:
--   The Dual Frames construction uses the hform eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DualOfDualFrames.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DualOfDualFrames.lean#L10-L13

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}

theorem GlobalTheory.DualFrames.hform_eq_dot (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    hform τ J x y = (τ ∘ x) ⬝ᵥ (J *ᵥ y) := by sorry
