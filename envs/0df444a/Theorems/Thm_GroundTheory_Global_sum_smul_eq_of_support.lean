-- Prove2me | Theorems.Thm_GroundTheory_Global_sum_smul_eq_of_support
-- name    : GroundTheory.Global.sum_smul_eq_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:27.385078+00:00
-- url     : https://prove2.me/theorems/98d7bc14-a7a6-4407-bf6e-9b2a7233cf73
-- title:
--   Global: sum smul eq of support
-- statement:
--   The Global construction uses the sum smul eq of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L78-L91

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
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
variable [Fintype G]

theorem GroundTheory.Global.sum_smul_eq_of_support (F : X → ℤ) (hF : ∀ y, F y ≠ 0 → orbitPoint G y = y) (p : X) :
    ∑ g : G, F (g • p) = Nat.card (stabilizer G p) * F (orbitPoint G p) := by sorry
