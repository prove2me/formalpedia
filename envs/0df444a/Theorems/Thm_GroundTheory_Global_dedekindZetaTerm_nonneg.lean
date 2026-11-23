-- Prove2me | Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
-- name    : GroundTheory.Global.dedekindZetaTerm_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:28.758467+00:00
-- url     : https://prove2.me/theorems/bbcb15aa-325e-4cc8-b573-c36ac08d6dee
-- title:
--   Global: dedekind Zeta Term nonneg
-- statement:
--   The Global construction uses the dedekind Zeta Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L18-L20

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

theorem GroundTheory.Global.dedekindZetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ dedekindZetaTerm K s n := by sorry
