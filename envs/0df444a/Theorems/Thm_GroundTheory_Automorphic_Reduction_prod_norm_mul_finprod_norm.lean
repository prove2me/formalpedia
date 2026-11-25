-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_prod_norm_mul_finprod_norm
-- name    : GroundTheory.Automorphic.Reduction.prod_norm_mul_finprod_norm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:32.749175+00:00
-- url     : https://prove2.me/theorems/dab647a9-bcfc-44ec-8be7-5a426949a525
-- title:
--   Reduction: prod norm mul finprod norm
-- statement:
--   The Reduction construction uses the prod norm mul finprod norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L225-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L225-L230

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

theorem GroundTheory.Automorphic.Reduction.prod_norm_mul_finprod_norm {c : K} (hc : c ≠ 0) :
    (∏ w : InfinitePlace K, ‖(c : w.Completion)‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(c : v.adicCompletion K)‖ = 1 := by sorry
