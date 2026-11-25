-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_euclidNorm
-- name    : GroundTheory.Automorphic.Reduction.norm_le_euclidNorm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:07:30.446308+00:00
-- url     : https://prove2.me/theorems/e4a67afc-97e1-485c-9215-b8d444e71e06
-- title:
--   Reduction: norm le euclid Norm
-- statement:
--   The Reduction construction uses the norm le euclid Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L22-L25

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

theorem GroundTheory.Automorphic.Reduction.norm_le_euclidNorm (y : Fin n → E) (i : Fin n) : ‖y i‖ ≤ euclidNorm y := by sorry
