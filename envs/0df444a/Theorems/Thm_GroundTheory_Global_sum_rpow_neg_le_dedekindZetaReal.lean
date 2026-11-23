-- Prove2me | Theorems.Thm_GroundTheory_Global_sum_rpow_neg_le_dedekindZetaReal
-- name    : GroundTheory.Global.sum_rpow_neg_le_dedekindZetaReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:32.934572+00:00
-- url     : https://prove2.me/theorems/24f0f762-d8c6-4297-a03b-45737769f396
-- title:
--   Global: sum rpow neg le dedekind Zeta Real
-- statement:
--   The Global construction uses the sum rpow neg le dedekind Zeta Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L235-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L235-L249

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

theorem GroundTheory.Global.sum_rpow_neg_le_dedekindZetaReal (T : Finset (Ideal (𝓞 K))) {s : ℝ}
    (hζ : Summable (dedekindZetaTerm K s)) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ dedekindZetaReal K s := by sorry
