-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetIndicator_dc_subset
-- name    : GlobalTheory.DoubleCosetIndicator.dc_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:18.423316+00:00
-- url     : https://prove2.me/theorems/048e145c-58cd-49af-a3ef-b01ae2445521
-- title:
--   Double Coset Indicator: dc subset
-- statement:
--   The Double Coset Indicator construction uses the dc subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqSumIndicator.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqSumIndicator.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetIndicator

theorem GlobalTheory.DoubleCosetIndicator.dc_subset {G : Type} [Group G] (R K : Subgroup G) {s t x : G}
    (hs : x ∈ dc R K s) (ht : x ∈ dc R K t) : dc R K s ⊆ dc R K t := by sorry
