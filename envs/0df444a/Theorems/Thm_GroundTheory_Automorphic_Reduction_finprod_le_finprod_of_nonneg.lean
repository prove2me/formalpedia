-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finprod_le_finprod_of_nonneg
-- name    : GroundTheory.Automorphic.Reduction.finprod_le_finprod_of_nonneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:01.19405+00:00
-- url     : https://prove2.me/theorems/63c989ff-d8da-4754-8f57-b3868036c264
-- title:
--   Reduction: finprod le finprod of nonneg
-- statement:
--   The Reduction construction uses the finprod le finprod of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L46-L54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
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
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.finprod_le_finprod_of_nonneg {α : Type*} {f g : α → ℝ}
    (hf : (Function.mulSupport f).Finite) (hg : (Function.mulSupport g).Finite)
    (h0 : ∀ a, 0 ≤ f a) (h : ∀ a, f a ≤ g a) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by sorry
