-- Prove2me | Theorems.Thm_GlobalTheory_DetIdeal_exists_det_ne_zero
-- name    : GlobalTheory.DetIdeal.exists_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:13.129809+00:00
-- url     : https://prove2.me/theorems/2ce9fa82-5c5a-4833-8aae-f46826aa6245
-- title:
--   Det Ideal: exists det ne zero
-- statement:
--   The Det Ideal construction uses the exists det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L213-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}

theorem GlobalTheory.DetIdeal.exists_det_ne_zero (S : Set (Fin r → K)) (hS : Submodule.span K S = ⊤) :
    ∃ Y : Matrix (Fin r) (Fin r) K, (∀ i, Y i ∈ S) ∧ Y.det ≠ 0 := by sorry
