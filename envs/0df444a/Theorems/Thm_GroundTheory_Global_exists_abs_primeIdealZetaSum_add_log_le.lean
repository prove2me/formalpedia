-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_abs_primeIdealZetaSum_add_log_le
-- name    : GroundTheory.Global.exists_abs_primeIdealZetaSum_add_log_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.354876+00:00
-- url     : https://prove2.me/theorems/b6f74e91-6182-4d21-a82c-cd00fe336407
-- title:
--   Global: exists abs prime Ideal Zeta Sum add log le
-- statement:
--   The Global construction uses the exists abs prime Ideal Zeta Sum add log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L320-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L320-L348

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
variable (K)

theorem GroundTheory.Global.exists_abs_primeIdealZetaSum_add_log_le :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s + Real.log (s - 1)| ≤ C := by sorry
