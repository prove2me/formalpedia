-- Prove2me | Theorems.Thm_GroundTheory_Global_t2Space_adeleRing
-- name    : GroundTheory.Global.t2Space_adeleRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:24.246854+00:00
-- url     : https://prove2.me/theorems/b06acf12-ff28-483e-9e74-f5c38ad80e95
-- title:
--   Global: t2 Space adele Ring
-- statement:
--   The Global construction uses the t2 Space adele Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Topology.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Topology.lean#L32-L33

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

theorem GroundTheory.Global.t2Space_adeleRing : T2Space 𝔸[K] := by sorry
