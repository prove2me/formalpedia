-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_finite_mulSupport
-- name    : GroundTheory.Automorphic.Reduction.HasFiniteContent.finite_mulSupport
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:38.987144+00:00
-- url     : https://prove2.me/theorems/ea0f4651-a626-447e-955a-7e6d50fc772b
-- title:
--   Has Finite Content: finite mul Support
-- statement:
--   The Has Finite Content construction uses the finite mul Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L123-L125

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

theorem GroundTheory.Automorphic.Reduction.HasFiniteContent.finite_mulSupport {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖finComp v y‖).Finite := by sorry
