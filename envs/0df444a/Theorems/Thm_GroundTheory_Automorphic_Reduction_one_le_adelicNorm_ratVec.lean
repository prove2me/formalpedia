-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_one_le_adelicNorm_ratVec
-- name    : GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:31.9628+00:00
-- url     : https://prove2.me/theorems/6a73ff0b-2184-4e25-85b0-735b63cac5e3
-- title:
--   Reduction: one le adelic Norm rat Vec
-- statement:
--   The Reduction construction uses the one le adelic Norm rat Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L232-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L232-L249

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

theorem GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ adelicNorm (ratVec x) := by sorry
