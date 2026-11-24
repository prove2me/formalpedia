-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_natDegree_minpoly_int_le
-- name    : GlobalTheory.MinpolyHeightCount.natDegree_minpoly_int_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:46.36489+00:00
-- url     : https://prove2.me/theorems/6741f1f9-df47-4a73-bfa4-b830b9d03da9
-- title:
--   Minpoly Height Count: nat Degree minpoly int le
-- statement:
--   The Minpoly Height Count construction uses the nat Degree minpoly int le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L51-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable (K : Type) [Field K] [NumberField K]

theorem GlobalTheory.MinpolyHeightCount.natDegree_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree ≤ Module.finrank ℚ K := by sorry
