-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveValuationProduct_addVal_prod
-- name    : GlobalTheory.AdditiveValuationProduct.addVal_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:53:40.281164+00:00
-- url     : https://prove2.me/theorems/c2593be3-c551-486b-9d04-d788d0d5b1aa
-- title:
--   Additive Valuation Product: add Val prod
-- statement:
--   The Additive Valuation Product construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/Imports.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/Imports.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.AdditiveValuationProduct

theorem GlobalTheory.AdditiveValuationProduct.addVal_prod : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by sorry
