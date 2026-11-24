-- Prove2me | Theorems.Thm_GroundTheory_Global_cyclicHerbrand_ofMulAction
-- name    : GroundTheory.Global.cyclicHerbrand_ofMulAction
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:28.206794+00:00
-- url     : https://prove2.me/theorems/4f3d83e0-d106-4e38-b1fb-82a725516c3d
-- title:
--   Global: cyclic Herbrand of Mul Action
-- statement:
--   The Global construction uses the cyclic Herbrand of Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L278-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L278-L283

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

theorem GroundTheory.Global.cyclicHerbrand_ofMulAction [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (Representation.ofMulAction ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by sorry
