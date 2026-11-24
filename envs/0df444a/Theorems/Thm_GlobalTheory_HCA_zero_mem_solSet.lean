-- Prove2me | Theorems.Thm_GlobalTheory_HCA_zero_mem_solSet
-- name    : GlobalTheory.HCA.zero_mem_solSet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:59:29.558898+00:00
-- url     : https://prove2.me/theorems/91d217b3-2a9b-4d71-9309-63cc37047d4a
-- title:
--   HCA: zero mem sol Set
-- statement:
--   The HCA construction uses the zero mem sol Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZeroMemSolSet.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZeroMemSolSet.lean#L40-L50

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg
open scoped BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
variable {d : ℕ}
open scoped BoundedContinuousFunction
variable {d : ℕ}

theorem GlobalTheory.HCA.zero_mem_solSet {ι : Type} (P : _root_.ZetaZeros.D.EllReg.Sys d ι) (U : Set (_root_.ZetaZeros.D.EllReg.E d)) :
    (0 : U →ᵇ ℂ) ∈ _root_.GlobalTheory.HCA.solSet P U := by sorry
