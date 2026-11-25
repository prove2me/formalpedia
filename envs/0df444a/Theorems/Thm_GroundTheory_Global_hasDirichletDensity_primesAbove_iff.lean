-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_primesAbove_iff
-- name    : GroundTheory.Global.hasDirichletDensity_primesAbove_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:16.011108+00:00
-- url     : https://prove2.me/theorems/57f1ba5d-9ad8-53bd-bd50-675a48e022db
-- title:
--   Global: has Dirichlet Density primes Above iff
-- statement:
--   The Global construction uses the has Dirichlet Density primes Above iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L271-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L271-L305

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
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
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

theorem GroundTheory.Global.hasDirichletDensity_primesAbove_iff {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) (δ : ℝ) :
    (primesAbove L T).HasDirichletDensity (Module.finrank K L * δ) ↔ T.HasDirichletDensity δ := by sorry
