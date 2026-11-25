-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_vecMul
-- name    : GroundTheory.Automorphic.Reduction.HasFiniteContent.vecMul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:11.929028+00:00
-- url     : https://prove2.me/theorems/ab22d70f-5c23-400a-be19-044eabfb1c0f
-- title:
--   Has Finite Content: vec Mul
-- statement:
--   The Has Finite Content construction uses the vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L182-L186

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

theorem GroundTheory.Automorphic.Reduction.HasFiniteContent.vecMul {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (g : AdelicGLn.AdelicGL K n) :
    HasFiniteContent (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by sorry
