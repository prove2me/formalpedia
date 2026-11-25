-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_coeff_lgSum
-- name    : GlobalTheory.ChainCoord.coeff_lgSum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:05.693448+00:00
-- url     : https://prove2.me/theorems/baf888cf-2d24-4bee-bfff-d58f27d4c55b
-- title:
--   Chain Coord: coeff lg Sum
-- statement:
--   The Chain Coord construction uses the coeff lg Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L89-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

theorem GlobalTheory.ChainCoord.coeff_lgSum {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0) (e : Fin d)
    (α : Fin M →₀ ℕ) (N : ℕ) (hN : Finsupp.degree α < N) :
    coeff α (lgSum l al t e) =
      ∑ n ∈ Finset.range N, ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := by sorry
