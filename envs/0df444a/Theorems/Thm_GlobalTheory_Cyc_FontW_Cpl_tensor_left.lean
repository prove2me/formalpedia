-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_tensor_left
-- name    : GlobalTheory.Cyc.FontW.Cpl.tensor_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:43.249815+00:00
-- url     : https://prove2.me/theorems/6ac7a805-1d1d-4111-a351-5798362cdbb6
-- title:
--   Cpl: tensor left
-- statement:
--   The Cpl construction uses the tensor left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L44-L50

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

theorem GlobalTheory.Cyc.FontW.Cpl.tensor_left {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by sorry
