-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_tensor_right
-- name    : GlobalTheory.Cyc.FontW.Cpl.tensor_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:15.564178+00:00
-- url     : https://prove2.me/theorems/5c1a9e1e-edcb-58da-9654-fbd88ccc1804
-- title:
--   Cpl: tensor right
-- statement:
--   The Cpl construction uses the tensor right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L52-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW

theorem GlobalTheory.Cyc.FontW.Cpl.tensor_right {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) := by sorry
