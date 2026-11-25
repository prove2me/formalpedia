-- Prove2me | Theorems.Thm_GroundTheory_Global_ker_normHom_le_range_cycSub_ofMulAction
-- name    : GroundTheory.Global.ker_normHom_le_range_cycSub_ofMulAction
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:18.221498+00:00
-- url     : https://prove2.me/theorems/f5950f21-8fb2-47e7-8a94-2430d2867d80
-- title:
--   Global: ker norm Hom le range cyc Sub of Mul Action
-- statement:
--   The Global construction uses the ker norm Hom le range cyc Sub of Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L135-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L135-L183

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}

theorem GroundTheory.Global.ker_normHom_le_range_cycSub_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (normHom (Representation.ofMulAction ℤ G X)).ker ≤
      (cycSub (Representation.ofMulAction ℤ G X) σ).range := by sorry
