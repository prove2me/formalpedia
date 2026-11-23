-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support
-- name    : GroundTheory.Automorphic.Whittaker.isCompact_support
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:33.715351+00:00
-- url     : https://prove2.me/theorems/4368abca-7f5e-44c9-9a30-13856a736f3b
-- title:
--   Whittaker: is Compact support
-- statement:
--   The Whittaker construction uses the is Compact support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L50-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]

theorem GroundTheory.Automorphic.Whittaker.isCompact_support {f : X → ℂ} (hf : f ∈ locallyConstantCompactSupport X ℂ ℂ) :
    IsCompact (Function.support f) := by sorry
