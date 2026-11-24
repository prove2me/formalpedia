-- Prove2me | Theorems.Thm_GroundTheory_Global_mk_orbitPoint
-- name    : GroundTheory.Global.mk_orbitPoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:12.146864+00:00
-- url     : https://prove2.me/theorems/2c4e76fe-1c85-464e-84fd-d4c35c7bcb8a
-- title:
--   Global: mk orbit Point
-- statement:
--   The Global construction uses the mk orbit Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L18-L20

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

theorem GroundTheory.Global.mk_orbitPoint (x : X) :
    Quotient.mk (orbitRel G X) (orbitPoint G x) = Quotient.mk (orbitRel G X) x := by sorry
