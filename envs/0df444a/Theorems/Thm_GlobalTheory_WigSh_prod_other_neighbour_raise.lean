-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_prod_other_neighbour_raise
-- name    : GlobalTheory.WigSh.prod_other_neighbour_raise
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:20.546696+00:00
-- url     : https://prove2.me/theorems/a8f7adc3-f7ee-598f-8e1c-a51d61e363ed
-- title:
--   Wig Sh: prod other neighbour raise
-- statement:
--   The Wig Sh construction uses the prod other neighbour raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqRaising.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqRaising.lean#L11-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaising
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh

theorem GlobalTheory.WigSh.prod_other_neighbour_raise {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by sorry
