-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_shortExact_map_toAbSheaf
-- name    : GlobalTheory.SheafLES.shortExact_map_toAbSheaf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:39.175568+00:00
-- url     : https://prove2.me/theorems/96c161bf-9428-44e6-8045-1cb988e4eb3f
-- title:
--   Sheaf LES: short Exact map to Ab Sheaf
-- statement:
--   The Sheaf LES construction uses the short Exact map to Ab Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L348-L350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
open AlgebraicGeometry
variable (X : Scheme.{u})
variable {X}

theorem GlobalTheory.SheafLES.shortExact_map_toAbSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheaf X)).ShortExact := by sorry
