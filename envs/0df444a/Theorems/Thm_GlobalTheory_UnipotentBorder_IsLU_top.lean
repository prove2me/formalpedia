-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_IsLU_top
-- name    : GlobalTheory.UnipotentBorder.IsLU.top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:05.436011+00:00
-- url     : https://prove2.me/theorems/d844073d-43ab-490a-809a-8ec8e1efc41e
-- title:
--   Is LU: top
-- statement:
--   The Is LU construction uses the top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L56-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]

theorem GlobalTheory.UnipotentBorder.IsLU.top {n : ℕ} {L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L) :
    IsLU (L.submatrix Fin.castSucc Fin.castSucc) := by sorry
