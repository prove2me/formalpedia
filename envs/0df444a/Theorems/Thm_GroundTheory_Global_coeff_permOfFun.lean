-- Prove2me | Theorems.Thm_GroundTheory_Global_coeff_permOfFun
-- name    : GroundTheory.Global.coeff_permOfFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:26.55671+00:00
-- url     : https://prove2.me/theorems/bc8f1bc0-23da-4246-af6c-08422f339e20
-- title:
--   Global: coeff perm Of Fun
-- statement:
--   The Global construction uses the coeff perm Of Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L109-L110

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
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]

theorem GroundTheory.Global.coeff_permOfFun [Finite X] (F : X → ℤ) (x : X) : (permOfFun F).coeff x = F x := by sorry
