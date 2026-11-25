-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicGL_ext
-- name    : GroundTheory.Automorphic.Reduction.adelicGL_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:10.507119+00:00
-- url     : https://prove2.me/theorems/5ba5000c-b195-433f-bc9a-4b1c4ebf6ae5
-- title:
--   Reduction: adelic GL ext
-- statement:
--   The Reduction construction uses the adelic GL ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L252-L255

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
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
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]

theorem GroundTheory.Automorphic.Reduction.adelicGL_ext {g h : AdelicGLn.AdelicGL K n} (h1 : ∀ w, infAt w g = infAt w h)
    (h2 : ∀ v, finAt v g = finAt v h) : g = h := by sorry
