-- Prove2me | Theorems.Thm_GroundTheory_Global_sum_range_dedekindZetaTerm
-- name    : GroundTheory.Global.sum_range_dedekindZetaTerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:37.011658+00:00
-- url     : https://prove2.me/theorems/2a5b6ede-48d9-410c-91ee-cab08b8c4169
-- title:
--   Global: sum range dedekind Zeta Term
-- statement:
--   The Global construction uses the sum range dedekind Zeta Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L52-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L52-L71

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

theorem GroundTheory.Global.sum_range_dedekindZetaTerm (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, dedekindZetaTerm K s n =
      ∑ I ∈ (finite_absNorm_lt K N).toFinset, (absNorm I : ℝ) ^ (-s) := by sorry
