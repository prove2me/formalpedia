-- Prove2me | Theorems.Thm_Neutral_B1_localIdele_neg_one_mem_rayUnits
-- name    : Neutral.B1.localIdele_neg_one_mem_rayUnits
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:34.004359+00:00
-- url     : https://prove2.me/theorems/2baf0101-39df-576a-8a3d-e1abd93c7261
-- title:
--   B1: local Idele neg one mem ray Units
-- statement:
--   The B1 construction uses the local Idele neg one mem ray Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L227-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L227-L240

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

theorem Neutral.B1.localIdele_neg_one_mem_rayUnits (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K))
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ m₀ ≤ v.asIdeal) :
    localIdele K v (-1) ∈ rayUnits K m₀ mInf ∧ localIdele K v (-1) ≠ 1 := by sorry
