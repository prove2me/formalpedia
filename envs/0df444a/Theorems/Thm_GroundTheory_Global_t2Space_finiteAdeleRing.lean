-- Prove2me | Theorems.Thm_GroundTheory_Global_t2Space_finiteAdeleRing
-- name    : GroundTheory.Global.t2Space_finiteAdeleRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:50.857124+00:00
-- url     : https://prove2.me/theorems/ec189550-50ff-4b49-9b54-ee8cabcb647e
-- title:
--   Global: t2 Space finite Adele Ring
-- statement:
--   The Global construction uses the t2 Space finite Adele Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Topology.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Topology.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 K) K) := by sorry
