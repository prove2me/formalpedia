-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_algebraMap
-- name    : GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:26:04.355803+00:00
-- url     : https://prove2.me/theorems/fb8b5e14-75f2-480b-96bf-c34a0e904f14
-- title:
--   Adele Base Change: finite Adele Map algebra Map
-- statement:
--   The Adele Base Change construction uses the finite Adele Map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L77-L81

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

theorem GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_algebraMap (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by sorry
