-- Prove2me | Theorems.Thm_GlobalTheory_MatchParts_tors_le
-- name    : GlobalTheory.MatchParts.tors_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:22:18.454346+00:00
-- url     : https://prove2.me/theorems/0610cf9d-e163-4f0c-ac06-5fe66d09acfc
-- title:
--   Match Parts: tors le
-- statement:
--   The Match Parts construction uses the tors le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L198-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L198-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem GlobalTheory.MatchParts.tors_le (μ : Match N N' n) (hn : 1 < n) {k a a' : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N.InG p → N'.InG p')
    (e : Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin a → ZMod k)))
    (e' : Nonempty ((powMonoidHom k : N'.Gt →* N'.Gt).ker ≃* Multiplicative (Fin a' → ZMod k))) : a ≤ a' := by sorry
