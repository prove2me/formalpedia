-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isZero_groupCohomology_galois
-- name    : GroundTheory.ProfCoh.isZero_groupCohomology_galois
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:50.980807+00:00
-- url     : https://prove2.me/theorems/3232e8a3-c171-4baf-a387-904fa08b6974
-- title:
--   Prof Coh: is Zero group Cohomology galois
-- statement:
--   The Prof Coh construction uses the is Zero group Cohomology galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory CategoryTheory.Limits
universe u
open groupCohomology
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

theorem GroundTheory.ProfCoh.isZero_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) := by sorry
