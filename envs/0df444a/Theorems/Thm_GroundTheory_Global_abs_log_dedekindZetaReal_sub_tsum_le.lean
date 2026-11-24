-- Prove2me | Theorems.Thm_GroundTheory_Global_abs_log_dedekindZetaReal_sub_tsum_le
-- name    : GroundTheory.Global.abs_log_dedekindZetaReal_sub_tsum_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:04.805415+00:00
-- url     : https://prove2.me/theorems/f1064eae-5d67-4376-a24b-26845d032fda
-- title:
--   Global: abs log dedekind Zeta Real sub tsum le
-- statement:
--   The Global construction uses the abs log dedekind Zeta Real sub tsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L264-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L264-L299

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

theorem GroundTheory.Global.abs_log_dedekindZetaReal_sub_tsum_le {s : ℝ} (hs : 1 < s)
    (hζ : Summable (dedekindZetaTerm K s)) :
    |Real.log (dedekindZetaReal K s) -
        ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s)| ≤
      2 * ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ)) := by sorry
