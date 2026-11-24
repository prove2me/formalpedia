-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_of_le_rationalPrimeUnder
-- name    : GroundTheory.Global.summable_of_le_rationalPrimeUnder
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:33.887053+00:00
-- url     : https://prove2.me/theorems/5956b5d9-936a-4c58-a105-b8afc42f8b42
-- title:
--   Global: summable of le rational Prime Under
-- statement:
--   The Global construction uses the summable of le rational Prime Under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L83-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L83-L106

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

theorem GroundTheory.Global.summable_of_le_rationalPrimeUnder (g : HeightOneSpectrum (𝓞 L) → ℝ) {h : ℕ → ℝ}
    (hg : ∀ w, 0 ≤ g w) (hh0 : ∀ n, 0 ≤ h n) (hh : Summable h)
    (hgh : ∀ w, g w ≤ h (rationalPrimeUnder w)) : Summable g := by sorry
