-- Prove2me | Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_mul
-- name    : GroundTheory.Global.homeomorphMixedSpace_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:44.979883+00:00
-- url     : https://prove2.me/theorems/3b5894d8-de82-59e6-a1c0-f36d231dc8bc
-- title:
--   Global: homeomorph Mixed Space mul
-- statement:
--   The Global construction uses the homeomorph Mixed Space mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L59-L61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
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
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]

theorem GroundTheory.Global.homeomorphMixedSpace_mul (x y : InfiniteAdeleRing K) :
    homeomorphMixedSpace K (x * y) = homeomorphMixedSpace K x * homeomorphMixedSpace K y := by sorry
