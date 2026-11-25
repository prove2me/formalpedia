-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_vecMul_GL
-- name    : GroundTheory.Automorphic.Reduction.infComp_vecMul_GL
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:31.192483+00:00
-- url     : https://prove2.me/theorems/a6a5279f-0a0c-4011-ab44-7a2c40b239d8
-- title:
--   Reduction: inf Comp vec Mul GL
-- statement:
--   The Reduction construction uses the inf Comp vec Mul GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L103-L107

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

theorem GroundTheory.Automorphic.Reduction.infComp_vecMul_GL (w : InfinitePlace K) (y : Fin n → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    infComp w (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      infComp w y ᵥ* (infAt w g : Matrix (Fin n) (Fin n) w.Completion) := by sorry
