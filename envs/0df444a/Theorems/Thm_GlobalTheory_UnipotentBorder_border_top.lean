-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_border_top
-- name    : GlobalTheory.UnipotentBorder.border_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:29.653116+00:00
-- url     : https://prove2.me/theorems/bb671b84-b7c5-4935-819f-6f066f8d4dc6
-- title:
--   Unipotent Border: border top
-- statement:
--   The Unipotent Border construction uses the border top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L135-L136

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
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]

theorem GlobalTheory.UnipotentBorder.border_top : (border A col row x).submatrix Fin.castSucc Fin.castSucc = A := by sorry
