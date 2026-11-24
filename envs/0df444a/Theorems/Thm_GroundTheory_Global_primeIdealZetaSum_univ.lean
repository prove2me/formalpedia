-- Prove2me | Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_univ
-- name    : GroundTheory.Global.primeIdealZetaSum_univ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:21.955165+00:00
-- url     : https://prove2.me/theorems/60c153b5-a744-4f05-b908-09d7c05b049e
-- title:
--   Global: prime Ideal Zeta Sum univ
-- statement:
--   The Global construction uses the prime Ideal Zeta Sum univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L312-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L312-L316

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

theorem GroundTheory.Global.primeIdealZetaSum_univ (s : ℝ) :
    (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s) := by sorry
