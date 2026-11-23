-- Prove2me | Theorems.Thm_Neutral_B1_valued_algebraMap_eq_one
-- name    : Neutral.B1.valued_algebraMap_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:21.822338+00:00
-- url     : https://prove2.me/theorems/6c073d6f-c3c0-4e1a-b006-c9b8fcacd8c0
-- title:
--   B1: valued algebra Map eq one
-- statement:
--   The B1 construction uses the valued algebra Map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L199-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L199-L205

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

theorem Neutral.B1.valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (y : K)) = 1 := by sorry
