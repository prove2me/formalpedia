-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_exact_map_toAbSheaf_iff
-- name    : GlobalTheory.SheafLES.exact_map_toAbSheaf_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:11:56.371941+00:00
-- url     : https://prove2.me/theorems/7f3914fc-ba49-4687-8ca6-56693175dd63
-- title:
--   Sheaf LES: exact map to Ab Sheaf iff
-- statement:
--   The Sheaf LES construction uses the exact map to Ab Sheaf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L352-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L352-L354

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

theorem GlobalTheory.SheafLES.exact_map_toAbSheaf_iff (S : ShortComplex X.Modules) :
    (S.map (toAbSheaf X)).Exact ↔ S.Exact := by sorry
