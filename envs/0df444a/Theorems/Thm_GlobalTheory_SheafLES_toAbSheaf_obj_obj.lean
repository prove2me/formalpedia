-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
-- name    : GlobalTheory.SheafLES.toAbSheaf_obj_obj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:36.499395+00:00
-- url     : https://prove2.me/theorems/83e04927-9960-43c7-ad6d-a550b73c61ae
-- title:
--   Sheaf LES: to Ab Sheaf obj obj
-- statement:
--   The Sheaf LES construction uses the to Ab Sheaf obj obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L343-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L343-L343

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

theorem GlobalTheory.SheafLES.toAbSheaf_obj_obj (M : X.Modules) : ((toAbSheaf X).obj M).obj = M.presheaf := by sorry

attribute [defeq] GlobalTheory.SheafLES.toAbSheaf_obj_obj
