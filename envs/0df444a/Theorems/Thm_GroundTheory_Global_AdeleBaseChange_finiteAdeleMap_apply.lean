-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
-- name    : GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:24:21.241226+00:00
-- url     : https://prove2.me/theorems/f0d03c1f-6dd0-4b6c-8494-c556c2337e16
-- title:
--   Adele Base Change: finite Adele Map apply
-- statement:
--   The Adele Base Change construction uses the finite Adele Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean#L69-L71

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

theorem GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply (x : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap K L x w = completionMap (below K w) w (x (below K w)) := by sorry

attribute [defeq] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
