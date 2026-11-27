-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_one_le_height_one
-- name    : GroundTheory.Automorphic.Reduction.one_le_height_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:27.887292+00:00
-- url     : https://prove2.me/theorems/ea93aeb4-a839-58a1-9ed5-6d9619db5fa3
-- title:
--   Reduction: one le height one
-- statement:
--   The Reduction construction uses the one le height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L277-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L277-L279

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.one_le_height_one {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ height 1 x := by sorry
