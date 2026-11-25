-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_HasValueAt_multiset_prod
-- name    : GlobalTheory.LGrp.HasValueAt.multiset_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:02.540275+00:00
-- url     : https://prove2.me/theorems/a9ac1232-7345-55da-8e52-ac13de0a6623
-- title:
--   Has Value At: multiset prod
-- statement:
--   The Has Value At construction uses the multiset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L94-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open Polynomial

theorem GlobalTheory.LGrp.HasValueAt.multiset_prod {ι : Type} (S : Multiset ι) {R : ι → RatFunc ℂ} {x : ℂ} {v : ι → ℂ}
    (h : ∀ i ∈ S, HasValueAt (R i) x (v i)) : HasValueAt (S.map R).prod x (S.map v).prod := by sorry
