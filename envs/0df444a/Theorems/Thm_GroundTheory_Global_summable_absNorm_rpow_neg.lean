-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg
-- name    : GroundTheory.Global.summable_absNorm_rpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:47.430525+00:00
-- url     : https://prove2.me/theorems/3e16de5c-bd75-4923-a19f-fbf970a15e7b
-- title:
--   Global: summable abs Norm rpow neg
-- statement:
--   The Global construction uses the summable abs Norm rpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L111-L117

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.summable_absNorm_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) := by sorry
