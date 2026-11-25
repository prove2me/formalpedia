-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_height_diagonal_mul
-- name    : GroundTheory.Automorphic.Reduction.height_diagonal_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:07.167784+00:00
-- url     : https://prove2.me/theorems/fa4e1afc-6bca-4068-86ae-2f8c5de416b6
-- title:
--   Reduction: height diagonal mul
-- statement:
--   The Reduction construction uses the height diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L272-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L272-L275

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

theorem GroundTheory.Automorphic.Reduction.height_diagonal_mul (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) :
    height (AdelicGLn.diagonal K n γ * g) x = height g (x ᵥ* (γ : Matrix (Fin n) (Fin n) K)) := by sorry
