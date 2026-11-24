-- Prove2me | Theorems.Thm_GroundTheory_Global_prod_one_add_rpow_neg_eq_sum
-- name    : GroundTheory.Global.prod_one_add_rpow_neg_eq_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:37.964209+00:00
-- url     : https://prove2.me/theorems/64a270a9-2fb7-43da-a3af-b84d72d673c7
-- title:
--   Global: prod one add rpow neg eq sum
-- statement:
--   The Global construction uses the prod one add rpow neg eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L214-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L214-L233

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

theorem GroundTheory.Global.prod_one_add_rpow_neg_eq_sum (P : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    ∏ w ∈ P, (1 + (absNorm w.asIdeal : ℝ) ^ (-s)) =
      ∑ I ∈ P.powerset.image (fun A => ∏ w ∈ A, w.asIdeal), (absNorm I : ℝ) ^ (-s) := by sorry
