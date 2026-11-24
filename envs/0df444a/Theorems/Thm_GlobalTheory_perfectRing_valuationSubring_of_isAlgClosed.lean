-- Prove2me | Theorems.Thm_GlobalTheory_perfectRing_valuationSubring_of_isAlgClosed
-- name    : GlobalTheory.perfectRing_valuationSubring_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:29.093049+00:00
-- url     : https://prove2.me/theorems/ef2bde80-ed4a-41ae-8a50-5793102fd5e6
-- title:
--   Global Theory: perfect Ring valuation Subring of is Alg Closed
-- statement:
--   The Global Theory construction uses the perfect Ring valuation Subring of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPoints.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPoints.lean#L9-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDomaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory

theorem GlobalTheory.perfectRing_valuationSubring_of_isAlgClosed (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by sorry
