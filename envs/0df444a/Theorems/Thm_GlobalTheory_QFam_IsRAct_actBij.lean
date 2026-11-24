-- Prove2me | Theorems.Thm_GlobalTheory_QFam_IsRAct_actBij
-- name    : GlobalTheory.QFam.IsRAct.actBij
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:37.150913+00:00
-- url     : https://prove2.me/theorems/4feed40c-0f8e-4866-8480-e97b6e12ae4a
-- title:
--   Is RAct: act Bij
-- statement:
--   The Is RAct construction uses the act Bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasQIff.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasQIff.lean#L46-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups ModularForm
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by sorry
