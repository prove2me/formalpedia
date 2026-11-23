-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_exists_sum
-- name    : GlobalTheory.FieldBaseChange.IsExtension.exists_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:13.832265+00:00
-- url     : https://prove2.me/theorems/b00c43da-7418-4669-a8b7-55c25c9ebaae
-- title:
--   Is Extension: exists sum
-- statement:
--   The Is Extension construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L91-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L91-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

theorem GlobalTheory.FieldBaseChange.IsExtension.exists_sum {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) (x : W) :
    ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i) := by sorry
