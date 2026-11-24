-- Prove2me | Theorems.Thm_GroundTheory_Global_rpow_neg_absNorm_le_half
-- name    : GroundTheory.Global.rpow_neg_absNorm_le_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:30.281486+00:00
-- url     : https://prove2.me/theorems/239fb95c-e02e-4527-a5ba-639f229554c4
-- title:
--   Global: rpow neg abs Norm le half
-- statement:
--   The Global construction uses the rpow neg abs Norm le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L105-L111

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

theorem GroundTheory.Global.rpow_neg_absNorm_le_half {p : Ideal (𝓞 K)} (hp : Prime p) {s : ℝ} (hs : 1 ≤ s) :
    (absNorm p : ℝ) ^ (-s) ≤ 1 / 2 := by sorry
