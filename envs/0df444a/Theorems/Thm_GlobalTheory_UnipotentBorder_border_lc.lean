-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_border_lc
-- name    : GlobalTheory.UnipotentBorder.border_lc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:06.677506+00:00
-- url     : https://prove2.me/theorems/7cbffce2-cae6-422b-82f2-3f73108728f0
-- title:
--   Unipotent Border: border lc
-- statement:
--   The Unipotent Border construction uses the border lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L132-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L132-L132

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

theorem GlobalTheory.UnipotentBorder.border_lc (j : Fin n) : border A col row x (Fin.last n) j.castSucc = row j := by sorry
