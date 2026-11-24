-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_exists_functional_det_map_ne_zero
-- name    : GlobalTheory.FieldBaseChange.exists_functional_det_map_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:28.893803+00:00
-- url     : https://prove2.me/theorems/8825cb6f-18d3-4830-9fed-24cb4d8d7cba
-- title:
--   Field Base Change: exists functional det map ne zero
-- statement:
--   The Field Base Change construction uses the exists functional det map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntertwiningBijectiveOfFieldBaseChange.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntertwiningBijectiveOfFieldBaseChange.lean#L10-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChange
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

theorem GlobalTheory.FieldBaseChange.exists_functional_det_map_ne_zero [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by sorry
