-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg_subtype
-- name    : GroundTheory.Global.summable_absNorm_rpow_neg_subtype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:30.56115+00:00
-- url     : https://prove2.me/theorems/967acf43-7545-4f43-afda-82f53951ac8c
-- title:
--   Global: summable abs Norm rpow neg subtype
-- statement:
--   The Global construction uses the summable abs Norm rpow neg subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L142-L144

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

theorem GroundTheory.Global.summable_absNorm_rpow_neg_subtype (S : Set (HeightOneSpectrum (𝓞 L))) {s : ℝ}
    (hs : 1 < s) : Summable fun w : S => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by sorry
