-- Prove2me | Theorems.Thm_Neutral_B1_one_mem_rayUnits
-- name    : Neutral.B1.one_mem_rayUnits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:05.937714+00:00
-- url     : https://prove2.me/theorems/8f525048-47c4-5519-bb4b-aa6e6bd6e46f
-- title:
--   B1: one mem ray Units
-- statement:
--   The B1 construction uses the one mem ray Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L163-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L163-L169

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

theorem Neutral.B1.one_mem_rayUnits (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K)) :
    (1 : Ideles K) ∈ rayUnits K m₀ mInf := by sorry
