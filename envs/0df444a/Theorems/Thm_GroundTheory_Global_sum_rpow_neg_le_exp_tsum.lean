-- Prove2me | Theorems.Thm_GroundTheory_Global_sum_rpow_neg_le_exp_tsum
-- name    : GroundTheory.Global.sum_rpow_neg_le_exp_tsum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:21.152198+00:00
-- url     : https://prove2.me/theorems/93f0b4c5-164a-4e86-8d2d-22a9a464ad8f
-- title:
--   Global: sum rpow neg le exp tsum
-- statement:
--   The Global construction uses the sum rpow neg le exp tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L127-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L127-L212

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.sum_rpow_neg_le_exp_tsum (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by sorry
