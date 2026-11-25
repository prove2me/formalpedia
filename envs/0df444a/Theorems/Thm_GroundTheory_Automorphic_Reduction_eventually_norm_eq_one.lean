-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_eq_one
-- name    : GroundTheory.Automorphic.Reduction.eventually_norm_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:45.647265+00:00
-- url     : https://prove2.me/theorems/349f218d-3b28-4ad7-a3cd-e4fc7d00c5a1
-- title:
--   Reduction: eventually norm eq one
-- statement:
--   The Reduction construction uses the eventually norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L211-L215

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

theorem GroundTheory.Automorphic.Reduction.eventually_norm_eq_one {k : K} (hk : k ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ = 1 := by sorry
