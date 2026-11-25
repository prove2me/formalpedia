-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_height
-- name    : GroundTheory.Automorphic.Reduction.hasFiniteContent_height
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:25.3703+00:00
-- url     : https://prove2.me/theorems/4acedf76-9e0b-47ad-ba59-fe2851d5500d
-- title:
--   Reduction: has Finite Content height
-- statement:
--   The Reduction construction uses the has Finite Content height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L260-L262

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

theorem GroundTheory.Automorphic.Reduction.hasFiniteContent_height (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) :
    HasFiniteContent (ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by sorry
