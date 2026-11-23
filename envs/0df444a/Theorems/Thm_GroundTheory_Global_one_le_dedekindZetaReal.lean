-- Prove2me | Theorems.Thm_GroundTheory_Global_one_le_dedekindZetaReal
-- name    : GroundTheory.Global.one_le_dedekindZetaReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:50.828935+00:00
-- url     : https://prove2.me/theorems/fa3ebd4d-0e08-4ca5-a5d9-e40e90f2ebcc
-- title:
--   Global: one le dedekind Zeta Real
-- statement:
--   The Global construction uses the one le dedekind Zeta Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L251-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L251-L254

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

theorem GroundTheory.Global.one_le_dedekindZetaReal {s : ℝ} (hζ : Summable (dedekindZetaTerm K s)) :
    1 ≤ dedekindZetaReal K s := by sorry
