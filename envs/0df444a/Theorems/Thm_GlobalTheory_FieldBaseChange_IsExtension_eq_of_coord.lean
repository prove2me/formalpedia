-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_eq_of_coord
-- name    : GlobalTheory.FieldBaseChange.IsExtension.eq_of_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:00.532992+00:00
-- url     : https://prove2.me/theorems/0e6b3165-db98-428f-b181-38bf2e9beeff
-- title:
--   Is Extension: eq of coord
-- statement:
--   The Is Extension construction uses the eq of coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L80-L89

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

theorem GlobalTheory.FieldBaseChange.IsExtension.eq_of_coord {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) {x y : W}
    (e : ∀ ℓ Λ, IsCoord a ℓ Λ → Λ x = Λ y) : x = y := by sorry
