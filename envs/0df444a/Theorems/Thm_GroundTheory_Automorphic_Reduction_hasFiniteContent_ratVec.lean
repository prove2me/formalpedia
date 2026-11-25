-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_ratVec
-- name    : GroundTheory.Automorphic.Reduction.hasFiniteContent_ratVec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:03.866186+00:00
-- url     : https://prove2.me/theorems/efdc2b42-6e8e-47c3-873e-c745840b0c58
-- title:
--   Reduction: has Finite Content rat Vec
-- statement:
--   The Reduction construction uses the has Finite Content rat Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L217-L223

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

theorem GroundTheory.Automorphic.Reduction.hasFiniteContent_ratVec {x : Fin n → K} (hx : x ≠ 0) : HasFiniteContent (ratVec x) := by sorry
