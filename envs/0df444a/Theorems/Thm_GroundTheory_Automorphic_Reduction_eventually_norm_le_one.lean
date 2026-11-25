-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_le_one
-- name    : GroundTheory.Automorphic.Reduction.eventually_norm_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:12.570166+00:00
-- url     : https://prove2.me/theorems/19b4995f-0906-466d-8a88-f9bcc13ca4b8
-- title:
--   Reduction: eventually norm le one
-- statement:
--   The Reduction construction uses the eventually norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L206-L209

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

theorem GroundTheory.Automorphic.Reduction.eventually_norm_le_one (k : K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ ≤ 1 := by sorry
