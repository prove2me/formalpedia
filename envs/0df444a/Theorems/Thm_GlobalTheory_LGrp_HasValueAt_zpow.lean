-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_HasValueAt_zpow
-- name    : GlobalTheory.LGrp.HasValueAt.zpow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:28.95404+00:00
-- url     : https://prove2.me/theorems/6c10c915-9b37-4f59-afc4-9225a36bfd3f
-- title:
--   Has Value At: zpow
-- statement:
--   The Has Value At construction uses the zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L88-L92

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

theorem GlobalTheory.LGrp.HasValueAt.zpow {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) (hv : v ≠ 0) (m : ℤ) :
    HasValueAt (R ^ m) x (v ^ m) := by sorry
