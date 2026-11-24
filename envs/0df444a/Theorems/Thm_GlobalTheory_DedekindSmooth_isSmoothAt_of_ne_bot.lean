-- Prove2me | Theorems.Thm_GlobalTheory_DedekindSmooth_isSmoothAt_of_ne_bot
-- name    : GlobalTheory.DedekindSmooth.isSmoothAt_of_ne_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:15.775969+00:00
-- url     : https://prove2.me/theorems/fd4178a1-391d-42c0-bf52-b4d6fe4b35d7
-- title:
--   Dedekind Smooth: is Smooth At of ne bot
-- statement:
--   The Dedekind Smooth construction uses the is Smooth At of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L37-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L37-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing

theorem GlobalTheory.DedekindSmooth.isSmoothAt_of_ne_bot (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [hqp : q.IsPrime]
    (hq : q ≠ ⊥) : Algebra.IsSmoothAt k q := by sorry
