-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_height_smul
-- name    : GroundTheory.Automorphic.Reduction.height_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:14.048663+00:00
-- url     : https://prove2.me/theorems/0a95d0dd-06b3-4f95-bd01-3d1a655e0702
-- title:
--   Reduction: height smul
-- statement:
--   The Reduction construction uses the height smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L267-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L267-L270

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

theorem GroundTheory.Automorphic.Reduction.height_smul (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) {c : K}
    (hc : c ≠ 0) : height g (c • x) = height g x := by sorry
