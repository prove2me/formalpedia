-- Prove2me | Theorems.Thm_GlobalTheory_DedekindSmooth_isSmoothAt_bot
-- name    : GlobalTheory.DedekindSmooth.isSmoothAt_bot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:37.087668+00:00
-- url     : https://prove2.me/theorems/f1016446-3f79-45ab-b9fc-a8185484b69e
-- title:
--   Dedekind Smooth: is Smooth At bot
-- statement:
--   The Dedekind Smooth construction uses the is Smooth At bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L7-L16

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

theorem GlobalTheory.DedekindSmooth.isSmoothAt_bot (k : Type) [Field k] [PerfectField k] (B : Type) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] : Algebra.IsSmoothAt k (⊥ : Ideal B) := by sorry
