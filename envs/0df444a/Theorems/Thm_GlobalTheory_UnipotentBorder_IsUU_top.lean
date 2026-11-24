-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_IsUU_top
-- name    : GlobalTheory.UnipotentBorder.IsUU.top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:22.824587+00:00
-- url     : https://prove2.me/theorems/3e655f32-1f49-41a8-871d-76caac254bc6
-- title:
--   Is UU: top
-- statement:
--   The Is UU construction uses the top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L52-L54

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

theorem GlobalTheory.UnipotentBorder.IsUU.top {n : ℕ} {U : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U) :
    IsUU (U.submatrix Fin.castSucc Fin.castSucc) := by sorry
