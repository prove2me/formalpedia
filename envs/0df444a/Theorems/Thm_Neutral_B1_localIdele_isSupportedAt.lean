-- Prove2me | Theorems.Thm_Neutral_B1_localIdele_isSupportedAt
-- name    : Neutral.B1.localIdele_isSupportedAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:21.671701+00:00
-- url     : https://prove2.me/theorems/7f1f4474-876e-443a-b621-caece30be466
-- title:
--   B1: local Idele is Supported At
-- statement:
--   The B1 construction uses the local Idele is Supported At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L192-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]

theorem Neutral.B1.localIdele_isSupportedAt (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    IsSupportedAt K (localIdele K v x) v := by sorry
