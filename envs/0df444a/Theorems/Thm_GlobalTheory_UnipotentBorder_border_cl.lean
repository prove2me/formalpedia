-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_border_cl
-- name    : GlobalTheory.UnipotentBorder.border_cl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:16.647255+00:00
-- url     : https://prove2.me/theorems/57d5c5a4-e051-4d30-bafa-a9eb0621d9c9
-- title:
--   Unipotent Border: border cl
-- statement:
--   The Unipotent Border construction uses the border cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L133-L133

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

theorem GlobalTheory.UnipotentBorder.border_cl (i : Fin n) : border A col row x i.castSucc (Fin.last n) = col i := by sorry
