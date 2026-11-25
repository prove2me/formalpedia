-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_groupCohomology_galois
-- name    : GroundTheory.ProfCoh.subsingleton_groupCohomology_galois
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:59.342801+00:00
-- url     : https://prove2.me/theorems/ebf7c438-3471-4d25-98c3-fd094bf8c164
-- title:
--   Prof Coh: subsingleton group Cohomology galois
-- statement:
--   The Prof Coh construction uses the subsingleton group Cohomology galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L81-L83

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

theorem GroundTheory.ProfCoh.subsingleton_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) := by sorry
