-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_smul
-- name    : GroundTheory.Automorphic.Reduction.euclidNorm_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:47.272639+00:00
-- url     : https://prove2.me/theorems/9b195f8c-ce2f-4072-8ec8-2c100284b20d
-- title:
--   Reduction: euclid Norm smul
-- statement:
--   The Reduction construction uses the euclid Norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L27-L29

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
variable {E : Type*} [NormedField E] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.euclidNorm_smul (c : E) (y : Fin n → E) : euclidNorm (c • y) = ‖c‖ * euclidNorm y := by sorry
