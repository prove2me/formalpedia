-- Prove2me | Theorems.Thm_GroundTheory_Global_card_filter_smul_eq
-- name    : GroundTheory.Global.card_filter_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:27.224728+00:00
-- url     : https://prove2.me/theorems/bc44a48d-aeaf-45ac-a9b6-0119388a8880
-- title:
--   Global: card filter smul eq
-- statement:
--   The Global construction uses the card filter smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L42-L58

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

theorem GroundTheory.Global.card_filter_smul_eq [DecidableEq X] (p : X) (g₀ : G) :
    (Finset.univ.filter fun g : G => g • p = g₀ • p).card = Nat.card (stabilizer G p) := by sorry
