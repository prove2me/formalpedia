-- Prove2me | Theorems.Thm_GroundTheory_Global_permOfFun_mem_ker
-- name    : GroundTheory.Global.permOfFun_mem_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:50.019804+00:00
-- url     : https://prove2.me/theorems/d46008a0-04f5-4e16-bc86-5e6eb8bbad20
-- title:
--   Global: perm Of Fun mem ker
-- statement:
--   The Global construction uses the perm Of Fun mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L129-L133

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
omit [Fintype G]

theorem GroundTheory.Global.permOfFun_mem_ker {F : X → ℤ} (hF : ∀ (g : G) x, F (g • x) = F x) :
    permOfFun F ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker := by sorry
