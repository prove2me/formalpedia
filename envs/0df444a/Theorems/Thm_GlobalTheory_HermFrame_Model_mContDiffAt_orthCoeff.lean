-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_Model_mContDiffAt_orthCoeff
-- name    : GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:17.169601+00:00
-- url     : https://prove2.me/theorems/634fe264-370f-4a71-87aa-47fddb98c38b
-- title:
--   Model: m Cont Diff At orth Coeff
-- statement:
--   The Model construction uses the m Cont Diff At orth Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l]

theorem GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthCoeff (H x)) z := by sorry
