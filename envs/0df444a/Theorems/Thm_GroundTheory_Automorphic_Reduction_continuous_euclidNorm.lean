-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_euclidNorm
-- name    : GroundTheory.Automorphic.Reduction.continuous_euclidNorm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:10:42.164794+00:00
-- url     : https://prove2.me/theorems/8a3da61a-f590-4ef4-bc36-6c7dfc9e0db3
-- title:
--   Reduction: continuous euclid Norm
-- statement:
--   The Reduction construction uses the continuous euclid Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L44-L46

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

theorem GroundTheory.Automorphic.Reduction.continuous_euclidNorm : Continuous (euclidNorm : (Fin n → E) → ℝ) := by sorry
