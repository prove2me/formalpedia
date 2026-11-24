-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_and_card_fiber_rationalPrimeUnder_le
-- name    : GroundTheory.Global.finite_and_card_fiber_rationalPrimeUnder_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:07.912931+00:00
-- url     : https://prove2.me/theorems/ea392dfd-dedd-4e3d-88ed-5d350292c738
-- title:
--   Global: finite and card fiber rational Prime Under le
-- statement:
--   The Global construction uses the finite and card fiber rational Prime Under le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L61-L81

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

theorem GroundTheory.Global.finite_and_card_fiber_rationalPrimeUnder_le (n : ℕ) :
    Finite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ∧
      Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ≤
        Module.finrank ℤ (𝓞 L) := by sorry
