-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteAdeleMap
-- name    : GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:26:41.137789+00:00
-- url     : https://prove2.me/theorems/d87caa0f-8c88-4963-b142-5aeb33f11d58
-- title:
--   Adele Base Change: continuous finite Adele Map
-- statement:
--   The Adele Base Change construction uses the continuous finite Adele Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L73-L75

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap : Continuous (finiteAdeleMap K L) := by sorry
