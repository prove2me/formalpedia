-- Prove2me | Theorems.Thm_GroundTheory_Global_orbitPoint_smul
-- name    : GroundTheory.Global.orbitPoint_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:35.132282+00:00
-- url     : https://prove2.me/theorems/7f13411f-7178-4dd3-9e2b-408109aca589
-- title:
--   Global: orbit Point smul
-- statement:
--   The Global construction uses the orbit Point smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L29-L30

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

theorem GroundTheory.Global.orbitPoint_smul (g : G) (x : X) : orbitPoint G (g • x) = orbitPoint G x := by sorry
