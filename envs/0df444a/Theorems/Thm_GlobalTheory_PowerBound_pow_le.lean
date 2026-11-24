-- Prove2me | Theorems.Thm_GlobalTheory_PowerBound_pow_le
-- name    : GlobalTheory.PowerBound.pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:57.742219+00:00
-- url     : https://prove2.me/theorems/5179aa5a-aa97-47a2-885a-6a3ed11505dd
-- title:
--   Power Bound: pow le
-- statement:
--   The Power Bound construction uses the pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Imports.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Imports.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerBound

theorem GlobalTheory.PowerBound.pow_le {A : Type} [CommRing A] (a d : A) (n : ℕ) :
    (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1) ≤
      Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by sorry
