-- Prove2me | Theorems.Thm_GroundTheory_Global_span_rationalPrimeUnder
-- name    : GroundTheory.Global.span_rationalPrimeUnder
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:09.100813+00:00
-- url     : https://prove2.me/theorems/c46ce230-e32e-4c4a-87db-e5bc8558f4b3
-- title:
--   Global: span rational Prime Under
-- statement:
--   The Global construction uses the span rational Prime Under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L37-L39

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
omit [NumberField L]

theorem GroundTheory.Global.span_rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.span {((rationalPrimeUnder w : ℕ) : ℤ)} = w.asIdeal.under ℤ := by sorry
