-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_kerModRange_normHom_ofMulAction
-- name    : GroundTheory.Global.natCard_kerModRange_normHom_ofMulAction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:34.190646+00:00
-- url     : https://prove2.me/theorems/907edfac-0548-4452-95cc-9ceebb11f923
-- title:
--   Global: nat Card ker Mod Range norm Hom of Mul Action
-- statement:
--   The Global construction uses the nat Card ker Mod Range norm Hom of Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L185-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L185-L196

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

theorem GroundTheory.Global.natCard_kerModRange_normHom_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) = 1 := by sorry
