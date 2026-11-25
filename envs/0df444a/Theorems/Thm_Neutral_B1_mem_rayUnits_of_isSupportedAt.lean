-- Prove2me | Theorems.Thm_Neutral_B1_mem_rayUnits_of_isSupportedAt
-- name    : Neutral.B1.mem_rayUnits_of_isSupportedAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:19.149783+00:00
-- url     : https://prove2.me/theorems/68a655a3-5cfd-4bda-a9f1-dfee9d36d72c
-- title:
--   B1: mem ray Units of is Supported At
-- statement:
--   The B1 construction uses the mem ray Units of is Supported At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L207-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L207-L225

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

theorem Neutral.B1.mem_rayUnits_of_isSupportedAt (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K))
    (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) (ha : IsSupportedAt K a v)
    (hv : ¬ m₀ ≤ v.asIdeal) (hu : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1) :
    a ∈ rayUnits K m₀ mInf := by sorry
