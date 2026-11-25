-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_depSet_idem_le
-- name    : GlobalTheory.GramCount.ncard_depSet_idem_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:10.268819+00:00
-- url     : https://prove2.me/theorems/4d39d8b7-b3db-475f-986b-71a857cd6444
-- title:
--   Gram Count: ncard dep Set idem le
-- statement:
--   The Gram Count construction uses the ncard dep Set idem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardDependentVectorsAffineGramLe.lean#L103-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardDependentVectorsAffineGramLe.lean#L103-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]

theorem GlobalTheory.GramCount.ncard_depSet_idem_le [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B}
    (hω : IsUnit (ω - c ω)) {q : ℕ} (hq : Fintype.card B = q ^ 2) {k n : ℕ}
    (x : Fin k → Fin n → B) (hx : Prim c x) (g : Fin k → B) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) : (depSet c x g ε).ncard ≤ q ^ n := by sorry
